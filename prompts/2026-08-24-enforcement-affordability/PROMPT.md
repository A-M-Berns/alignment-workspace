# Round: enforcement affordability — for which constraint schedules is bounded lifetime liability achievable?

Research round under `projects/normativity/`. Proposed round directory:
`projects/normativity/rounds/2026-08-24-enforcement-affordability/`.

All standards in `AGENTS.md` bind. Exact rational arithmetic throughout. Nothing
in this round is registered; every claim is `ci-only` unless promoted later by
the maintainer. All new names are provisional and queued in `DECISIONS.md`.

## The question

The paper skeleton (*Strengthening Logical Induction with Traderized
Constraints*, v44) makes bounded lifetime liability the hypothesis that buys
criterion preservation (its Theorem 4.5), verifies it only for the deductive
zero-liability case (Theorem 4.6), and bounds the general case per-day
(Proposition 6.1) plus a homothetic-core sufficient condition (Remark 6.2).
Prop 6.1's bound diverges for any constraint that permanently excludes
plausible payoff patterns — i.e., for every genuinely normative constraint.

The round's question: **is that divergence real, or an artifact of per-day
worst-case accounting?** Characterize which constraint schedules have bounded
lifetime liability, with exact finite witnesses on both sides. The central
proposed mechanism, to be prosecuted rather than assumed: liability is a
function of *realized* enforcement inventory against *budget-throttled*
opposing flow, not of available intensity λ_n — so affordability is governed by
the opposition's finite war chest and the peg's geometry, not by the tolerance
schedule.

**This round is licensed to kill.** The three headline claims under prosecution
(trichotomy, tolerance-independence, the exploitation identity below) were
produced in a single unaudited derivation. Refuting any of them with a minimal
witness is a full success of the round. Do not repair a claim silently; a
failed target ships as its counterexample plus the strongest revised statement
the counterexample permits.

## Pinned inputs

- The v44 skeleton (maintainer supplies the PDF/tex; treat as frozen input with
  checksum).
- `lean/Workspace/Normativity/Contrib/` at current main, in particular
  `AssessmentFirm.lean` (`componentTrader_netWorth_floor`,
  `tradingFirmTrader_netWorth_floor`) and `AssessmentProcess.lean`
  (`budgetedTrader`, `budgetedTrader_netWorth_floor`).
- The pinned source formalization's TradingFirm/Budgeter (via the FAF pin), for
  the deductive specialization check in G1.

Model discipline: build ONE exact finite market model in `src/` implementing
the day-local structure the skeleton actually uses — finite sentence support,
[0,1]∩ℚ prices, the MarketMaker guarantee as the fixed-point postulate (the
returned price state gives the presented day strategy value ≤ 2^-n at every
[0,1]-valuation on its support), budgeted component traders with the
per-component scaling semantics confirmed in G1, and the projection enforcer of
skeleton Definitions 2.2/3.6. Every fixture below runs through this one model.
No floats anywhere, including exploration code.

## Tier 1 — honesty gates (run first; everything downstream cites them)

- **G1 (budgeter semantics).** Read `budgetedTrader` in the workspace lift and
  the corresponding construction in the pinned source. Confirm or refute, with
  file/line citations in the memo: (a) the budget is enforced by per-component
  trade scaling computed from the realized price history, not by firm-level
  P&L netting; (b) the floor lemmas quantify over arbitrary [0,1]-rational
  histories, with no dependence on the prices arising from the unmodified
  recursion; (c) the assessment-process `Live` specialization recovers
  plausible-at-horizon `PC(D_N)` for deductive processes. If any of (a)–(c)
  fails, STOP the positive tier and report: the failure mode and its blast
  radius is the round's primary deliverable.
- **G2 (aggregation).** Establish exactly which statement caps a *distributed*
  attack: confirm that the component floors −(1/2)^j sum to the −2 firm floor
  independent of how adversarial flow is spread across components, and that a
  confederate component's gains cannot relax another component's throttle
  (mechanical scaling vs accounting offset). Produce the two-attacker fixture
  demonstrating both.

## Tier 2 — positive bounds (each: exact model theorem + adversarial fixtures)

- **T1 (uncontested conformity).** One undecided sentence, no firm interest,
  K = [3/5, 9/10], arbitrary δ. Prove in the model: the fixed-point price lies
  within O(2^-n) of K and the enforcer's realized position is O(2^-n);
  cumulative liability against EVERY world (plausible or not) is bounded by an
  explicit geometric sum. Note explicitly that this strengthens skeleton
  Theorem 3.4 in the uncontested case (distance ≈ 2^-n, not δ).
- **T2 (contested interior peg, the load-bearing target).** One never-deciding
  sentence, K = [2/5, 3/5], an adversarial budgeted component shorting
  relentlessly. Prove in the model: lifetime liability ≤
  (aggregate budget) · (far-side distance / near-side margin) + geometric
  slack, **with no dependence on the tolerance schedule** — verify the bound
  numerically identical under δ_n = 1/2, 1/n, 2^-n. Required adversarial
  fixtures, each with the bound intact or the counterexample shipped:
  (i) maximal-flow short; (ii) confederate pair per G2; (iii) dispersed swarm
  across many components; (iv) oscillation/churn attack — and verify the
  model exhibits the enforcer *earning* the region's width as spread against
  round-trip flow; (v) the δ→0 sequence.
- **T3 (margin definition).** Formalize the margin as: K_n ⊆ K^D_n AND every
  plausible payoff pattern at distance ≥ m from K_n, measured in the relative
  geometry (settled coordinates excluded). Show with a two-coordinate fixture
  that dropping the containment clause lets the model's coherence flow attack
  the peg unthrottled, and dropping the distance clause reproduces the W2
  blow-up. Both clauses necessary, separately witnessed.

## Tier 3 — divergence witnesses (parameterized, not just limiting)

- **W1 (anti-settlement).** φ settled true, K = [0, 3/10]. Exhibit unbounded
  liability driven by flow that no plausible world bills. State the
  companion observation: divergence here is FORCED by the skeleton's Theorem
  4.4 contrapositive (a criterion-preserving market cannot hold this peg);
  cite, don't re-prove.
- **W2 (dogmatism).** K = {ε} with both worlds plausible; exhibit liability
  growth ~ 1/margin as ε → 0, as a parameterized family with the rate
  displayed, not only the limit.
- **W3 (revision pump).** K jumps [1/10, 1/5] → [4/5, 9/10] repeatedly.
  Exhibit the cycle extracting world-uniform cash ≈ (jump − worst-plausible
  entry) per unit, and liability growth linear in total variation. Do NOT
  attempt the full motion-tagged TV bound (settlement-forced vs
  certificate-backed vs residual) — record it as the named follow-up; this
  round only witnesses that unbounded unaccounted motion diverges.
- **W4 (settlement surprise).** A norm coordinate entangled with a settling
  sentence: interior margin satisfied every day, then settlement kills the
  billing world. Exhibit the enforcer loss = inventory × mispricing at the
  settlement event, and unbounded total over a stream of such events. State
  the positive complement: on schedules confined to never-settling
  coordinates the term vanishes identically.

## Tier 4 — the identity probe

Proposed identity: bounded lifetime liability ⟺ no component (and no
coalition of components) achieves cumulative value against the enforcement
trades that is bounded below and unbounded above uniformly over
plausible-at-horizon worlds. Prosecute BOTH directions in the model. Required
attack: a trader whose income against the enforcer is uniform over the worlds
plausible *at each day* but not over worlds plausible at the horizon
(plausibility moves). If the attack succeeds, report which quantifier
(per-day vs at-horizon plausibility; individual vs ecology) the surviving
identity needs.

## Deliverables

- `MEMO.md` — every target graded: `proved-in-model` / `bound-with-argument` /
  `refuted (witness)` / `open`, with the G1 citations, and a candidate
  theorem-and-proof-sketch section for the SINGLE-COORDINATE trichotomy
  suitable for skeleton §6, clearly marked as paper-facing prose the
  maintainer may adapt.
- `THEOREM_MAP.md` — model statement ↔ skeleton statement ↔ (where they
  exist) Lean declarations; explicitly list which skeleton results are
  cited vs strengthened vs untouched.
- `src/` exact model, `tests/` (every fixture above is a test; target the
  usual adversarial density), `PROVENANCE.md`, `README.md` with run
  instructions.
- DECISIONS queue entries for provisional names. Do not coin beyond need;
  flag for the maintainer: names are wanted for the margin notion, the
  budget/war-chest quantity, and the trichotomy's three regimes.

## Out of scope (named so they are not silently attempted)

Multi-coordinate cross-subsidy closure beyond the G2 fixtures; the motion-tag
TV/surprise interaction (double-billing); anything touching the reason-state
waist, the frontier compiler, or value positions; Lean formalization (unless a
statement falls out in under an hour against the existing Contrib modules, in
which case take it and say so).

---

*Sent mid-round, before any fixture had run:*

# Addendum: the maintainer's two-defect taxonomy, and the fixtures that adjudicate it

Append to `PROMPT-enforcement-affordability.md`. Where this addendum and the
main prompt conflict, this addendum wins.

## The taxonomy under test

The maintainer proposes that a constraint schedule can be poorly behaved in
exactly two ways, and this round should treat the proposal as the organizing
hypothesis for the whole memo:

1. **Geometric defects** — a defect of where a single day's region sits.
   Candidate example: a point region such as K = {1/2}, which has no
   homothetic core, so the skeleton's Remark 6.2 accounting suggests per-day
   blow-up at low tolerance.
2. **Diachronic defects** — a defect of the time evolution. Candidate
   example: a schedule oscillating between p ≤ 1/10 and p ≥ 9/10 forever,
   which appears to force exploitability and therefore cannot be enforced
   criterion-preservingly.

The round's job is to determine, with exact witnesses: (a) whether these two
classes are exhaustive; (b) what the correct *general characterization* of
each class is; and (c) where the two competing accounts of the geometric
class disagree — and which one is right.

## The registered disagreement (adjudicate first within Tier 2)

Two accounts of geometric defectiveness make opposite predictions on one
fixture, and this is the single most informative test in the round:

- **Core account** (per-day, skeleton Remark 6.2): defectiveness ≈ absence of
  a homothetic core. Predicts K = {1/2} is defective: λ_n = ρ_n/δ_n² blows up
  as δ_n → 0 and per-day worst-case liability diverges.
- **Margin account** (flow-based, this round's central mechanism):
  defectiveness ≈ proximity of K_n to the plausible payoff patterns (and
  escape from the deductive region). Predicts K = {1/2} is AFFORDABLE
  uniformly in δ: both plausible vertices sit at distance 1/2, any attack
  pays ~1/2 per share against the far-side plausible world, the budgeter
  throttles the flow, and the large available λ never becomes a large
  realized position at the fixed point. On this account {1/2} and [2/5, 3/5]
  differ in *revenue* (a zero-width region earns no spread against churn),
  never in *solvency*; the genuinely defective point regions are the
  near-vertex ones, K = {ε}.

**Required fixture T2(vi):** point peg K = {1/2}, zero width, one undecided
sentence, adversarial flow per T2(i), run across all three tolerance
schedules (δ_n = 1/2, 1/n, 2^-n). Decision rule, stated in advance:
- liability flat across the δ schedules ⟹ margin account wins; record that
  homothetic core is sufficient-but-not-necessary and that the core lens
  mistakes a revenue property for a solvency property;
- liability growing as δ shrinks ⟹ core account wins; tolerance-independence
  (T2's headline) is REFUTED — report the mechanism by which available
  intensity converts to realized loss, since that failure invalidates the
  round's central flow argument well beyond this fixture.

Also run the same fixture at K = {ε} for a decreasing ε family to confirm
both accounts agree at the vertex (blow-up ~ 1/margin), so the disagreement
is isolated to the center.

## Diachronic class: what to establish beyond W3/W4

The maintainer's oscillation example is W3 nearly verbatim; keep it, and add
the exploitability reading explicitly: show the revision pump is not merely
costly but constitutes exploitation of the pricing sequence in the skeleton's
sense (value bounded below, unbounded above on plausible worlds), so that
divergence is FORCED by Theorem 4.4's contrapositive — the diachronic twin of
W1. Both bad poles should end the memo as "cannot be enforced by ANY
criterion-preserving construction," not "this construction fails."

Candidate general characterization to test, not assume: diachronic cost is
governed by the schedule's total variation Σ_n d_H(K_n, K_{n+1}), LESS motion
forced by settlement (when a coordinate settles, containment in K^D compels
the region to move; billing that motion punishes obedience — exhibit the
fixture where a prompt settlement-tracking move is free and a delayed one is
billed as W4 surprise). Two probes:

- **Bounded-TV positive probe:** a schedule with infinitely many moves but
  summable total variation (e.g. jumps of size 4^-k), interior margin
  maintained throughout. The margin account predicts bounded liability.
  If it diverges, total variation is the wrong diachronic functional —
  report what the pump actually extracts per cycle as a function of jump
  size and entry cost, and propose the corrected functional.
- **Frequency-vs-amplitude probe:** rapid small oscillation within a fixed
  interior band (K alternating [2/5, 1/2] and [1/2, 3/5]) versus the
  maintainer's full-swing oscillation. The account predicts the first is
  cheap (small per-cycle extraction) and the second fatal; if frequency
  alone can drive divergence at small amplitude, the path-length picture is
  wrong in an important way.

## Exhaustiveness probe

The taxonomy claims two classes. W4 (settlement surprise) sits awkwardly: the
schedule is geometrically perfect every day and the schedule itself never
moves — the DEDUCTIVE region moves. The memo must take a position, with a
fixture behind it, on whether W4 is (a) a third class, (b) the diachronic
class correctly generalized — defects of the co-evolution of the pair
(K_n, K^D_n) rather than of K_n's own path — or (c) reducible to a geometric
defect under the right relative-geometry margin definition (T3's, measured
against the surviving directions only). The round's recommendation on
(a)/(b)/(c) is a primary deliverable; it determines how the paper's §6 states
the trichotomy and how the frontier compiler's certificate is organized.

## Memo organization

Organize the final memo BY THE TAXONOMY: one part per defect class, each
part opening with the class's general characterization as best the evidence
supports it, the witnesses that pin it, and the boundary cases that resist
it. The single-coordinate trichotomy sketch requested in the main prompt
becomes the synthesis section across both parts.
