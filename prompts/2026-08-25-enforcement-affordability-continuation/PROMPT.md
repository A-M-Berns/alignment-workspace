# Continuation round on enforcement affordability (PR #50) — cold-start dispatch

You are NOT the author of the parent round. A prior agent produced the round
at `projects/normativity/rounds/2026-08-24-enforcement-affordability/` on
branch `round/2026-08-24-enforcement-affordability`; that agent's session is
gone, and everything that matters is on the branch. Before writing anything:

1. Read the parent round's `README.md`, `MEMO.md`, and `THEOREM_MAP.md` in
   full, and skim `src/market_model.py` until you understand the model's
   accounting (prices, components, budget scaling, enforcement coefficients,
   the MarketMaker fixed-point check).
2. Run `python3 tests/run.py` from the repository root and confirm the full
   suite is green in your environment before any edit.
3. Treat the parent's `proved-in-model` grades as standing claims: you may
   spot-check any of them, and you must report if a spot-check fails, but do
   not re-litigate the parent round wholesale. Your job is the continuation
   targets below.

You extend the SAME round directory in place: same model, new fixtures
appended under `tests/`, `MEMO.md` extended with clearly-marked continuation
sections, `THEOREM_MAP.md` extended, `PROVENANCE.md` updated with your own
generator row. The parent's grades and text are not edited. All standards in
`AGENTS.md` bind. Exact rational arithmetic everywhere. Nothing is
registered; every claim is `ci-only`. New names are provisional and queued in
`DECISIONS.md`.

## Context you need

The traderization paper (skeleton: *Strengthening Logical Induction with
Traderized Constraints*, v44 — the maintainer supplies it as a pinned input;
record its checksum in PROVENANCE) is being finished under an adopted split:
paper 1 keeps the liability interface plus ONE real nonzero-liability theorem
and ONE criterion-forced impossibility; the general affordability
characterization (trichotomy, diachronic functionals, recharge) is a
follow-up paper. Your continuation produces the paper-1 material. C0 is the
primary deliverable; C1 is its required supporting lemma; C2–C3 are
secondary and cheap-only; C4 is a collection file, not a work item.

Pinned Lean inputs (cite by file:line as the parent's §0 does):
`lean/Workspace/Normativity/Contrib/AssessmentFirm.lean` (component and firm
netWorth floors), `AssessmentProcess.lean` (`budgetedTrader`, its floor, the
deductive specialization), and the parent MEMO's §0 citation block, which
you should verify still resolves against the current tree.

## C0 — Skeleton-facing one-coordinate affordability theorem (PRIMARY)

Restate and prove, against the SKELETON'S OWN OBJECTS — MarketMaker
Definition/Proposition 5.1.2 via the skeleton's Lemma 3.2, Proposition 3.1,
the projection trade of Definition 2.2, and the Budgeter/TradingFirm
accounting per the pinned floor lemmas — the parent round's T2 result:

> For a single-sentence constraint schedule with plausibility margin ≥ m > 0
> on contested days and regions contained in the day's deductive region,
> enforcement has bounded lifetime liability, with a bound controlled by the
> opposition's cumulative plausible-downside budget and the peg geometry —
> and NOT by the tolerance schedule.

Deliverables:
- Theorem statement + full proof sketch in skeleton notation, written as
  paper-facing prose the maintainer may adapt, clearly marked as such.
- Every proof step tagged with (a) the parent-round fixture (test class
  name) that verifies it in the model, and (b) the existing Contrib lemma
  (file:line) it would compose from in a Lean promotion — plus an honest
  list of the steps with NO existing Lean support.
- The impossibility half, same standard: promote the parent's W1
  anti-settlement example to a skeleton-facing proposition — an explicit
  exploiter, cumulative value floored below and world-uniformly unbounded
  above on plausible worlds, hence by the skeleton's Theorem 4.4
  contrapositive NO criterion-preserving market enforces the schedule.
- The worked example pair for the section: K = {1/2} affordable uniformly
  in tolerance vs K = {ε} blowing up as 1/margin, citing the parent's
  T2(vi) and W2 fixtures.

## C1 — The self-financing lemma C0 needs (REQUIRED SUPPORT)

Even a single constrained sentence sits inside a firm trading OTHER
sentences: a component's wealth is global, so income minted elsewhere can
relax its throttle on the constrained coordinate. C0's bound is honest only
if this recycling channel is closed or explicitly parameterized:

- Enumerate the income sources available to opposing flow: MarketMaker
  slack (Σ 2^-n), other budgeted components (each bounded by its own
  floor), and the enforcer's own losses (the very quantity being bounded).
  Derive the self-referential bound — schematically
  L ≤ (chest + slack + κ·L) / margin-form — and determine when it closes
  (recycling coefficient κ below the margin term). Build the two-sentence
  fixture where an attacker actively recycles realized enforcer losses into
  further attack, and verify which side of the fork the model lands on.
- If the inequality does NOT close unconditionally: the deliverable is the
  PARAMETERIZED-CHEST form of C0 — "against any opposing flow of cumulative
  plausible downside ≤ W, liability ≤ W·C(geometry) + slack" — which is
  unconditionally true. State the fork plainly in the C0 prose; the
  maintainer chooses the presentation. Do NOT invent new fencing or
  budgeter modifications to force closure.

## C2 — Appendix D sharpness packaging (SECONDARY, paper 1)

Package the parent's alternating-singletons witness (Tier 4) as a
self-contained subsection the maintainer can adapt into the skeleton's
Appendix D: without support-local nesting — exactly Theorem D.1's
hypothesis — the liability–exploitation correspondence severs (day-uniform
income never becomes horizon upside while liability stays bounded). One
paragraph on what nesting buys beyond bookkeeping. Optionally, ONLY if
cheap: spot-check the C0 bound against one non-deductive nested assessment
so §6 could be stated at Appendix D's generality; otherwise record in C4.

## C3 — Converse of Theorem 4.6 as a remark (SECONDARY, cheap only)

Test the flow-quantified biconditional: zero liability against ALL budgeted
flow ⟺ every plausible pattern absorbed. Positive direction via a minimal
opposing component forcing loss bounded below by an explicit positive
function of (margin, flow size) at the excluded pattern's world. If it
lands cleanly, deliver as a two-sentence remark for §6. If any fixture
resists, record the witness in C4 and stop — this item must not expand.

## C4 — `FOLLOWUP_STOCK.md` (COLLECT, DO NOT DEVELOP)

Anything discovered en route that belongs to the general characterization —
multi-coordinate joint-margin behavior, recharge composition, set-gap
generalities, anything from a C2/C3 overflow — goes into a clearly-marked
`FOLLOWUP_STOCK.md` in the round directory, with fixture pointers,
undeveloped. The follow-up paper starts from that file; this round does not
write any of it.

## Out of scope

The full multi-coordinate cross-subsidy program; the motion-tag
decomposition; anything touching the record side, charges, or the
reason-state waist; set-gap vs movement-liability comparison; value
positions; related-work positioning (maintainer's task). No heroic repairs
anywhere: a fork or a failed fixture reported plainly is a complete
deliverable.

## Deliverables recap

Extended `MEMO.md` (continuation sections C0–C3, graded
`proved-in-model` / `bound-with-argument` / `refuted (witness)` / `open`,
with C0's paper-facing prose clearly marked), extended `THEOREM_MAP.md`
(which skeleton statements C0/C2/C3 strengthen; the Lean-promotion table
for C0 with file:line composition targets and named gaps),
`FOLLOWUP_STOCK.md`, new fixtures discovered by the round runner (suite
green end to end, including the repo-level `python3 tests/run.py`),
updated `PROVENANCE.md` with your generator row. The parent round's grades
and text are untouched.
