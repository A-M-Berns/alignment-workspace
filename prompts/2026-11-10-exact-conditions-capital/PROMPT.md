# Exact conditions on logical inductors — a formalization round

A new round on `A-M-Berns/alignment-workspace`, branched from the current `origin/main`.
Work in a fresh git worktree, on one branch named
`round/2026-11-10-exact-conditions-capital`. Open a pull request against `main`.
**Do not merge it and do not enable auto-merge**; the merge is the maintainer's.

Commit this prompt verbatim as `prompts/2026-11-10-exact-conditions-capital/PROMPT.md`
in the first commit. Prompt author: Claude Fable 5.2 (Anthropic), on the maintainer's
instruction in conversation on 2026-11-10. Identify the executing model accurately in
the report and the commit trailers.

**This round is a proof attempt.** The theorem arc below came out of a conversation and
three reviews by GPT-6 Astra (OpenAI). Every statement in it was checked by hand at
most; none is kernel-checked. Some have already been found false and repaired twice.
Your job is to find out which survive Lean. A statement that turns out false is a
result: report the counterexample and the strongest corrected statement you can prove.
Do not weaken a statement silently to make it provable; declare each change.

## The idea, in plain terms

A *condition* restricts which prices the reasoner may post on each day: a nonempty
rational polytope, equivalently finitely many *demanded bets* whose price must be
nonnegative. To honour a condition, the market must absorb whatever the trading firm
would do against it. The cumulative value of what it absorbs is one scalar *account*.
The condition is compatible with logical induction when that account stays bounded
below. A *reserve* is a way of certifying that; a *bounded-upside book* is a way of
refuting it. The existing force layer (`ProjectionForce`, `WarrantForce`) adds a
penalty trader and gets conformance within a tolerance; this round formalizes the exact
version, in which the market maker is constrained and the account is a dual
certificate, as an **interface** over an arbitrary price history, so that nothing here
depends on first constructing the constrained market maker.

## What already exists and should be reused

Under `lean/Workspace/Normativity/Contrib/`: `AssessmentProcess` (assessments, live
worlds, exploitation), `AssessmentFirm` (`TradingFirm`, `tradingFirmTrader_netWorth_floor`
and `trading_firm_dominance`, both stated for an arbitrary history `P`,
`isLogicalInductor_of_computableMarket`), `EnforcementPreservation`,
`DeductiveEnforcement`, `DeductiveRegion`, `NormativeInductorComposition` (`Row`,
`Bundle`, `Bundle.Region`, `FarkasCert`), `SeedStatics`, `WarrantEntitlement` /
`OddsBankroll` (the odds bankroll), `WarrantSolvency`. Read these before defining
anything; prefer their types to new ones, and say in the report where a new type
duplicates an old one and why.

## The theorem arc

Notation. An assessment `L`; a rational price history `P`; for each day `n` a finite
list of rows `g_{n,j}(x) = a_{n,j}·x + b_{n,j}` over sentence coordinates, the day's
region `K_n` being the cube points where every row is nonnegative; multipliers
`mu_{n,j} >= 0`; `q_n(W) = sum_j mu_{n,j} g_{n,j}(W)`; the account
`Q_N(W) = sum_{n<=N} q_n(W)`; `F_N(W)` the realized trading firm's cumulative value on
`P`; tolerances `eps_n > 0` with `sum eps_n = eps` finite; `U = 2 + eps`.

### Tier A — the interface and its consequences (the round's core)

**A0. The interface.** A structure (provisional name `DualCertifiedMarket`) carrying
`L`, `P`, the rows, the multipliers, exact membership `P_n ∈ K_n` on every day, and the
*day inequality*: for every valuation `w` of the day's coordinates in the cube,
`(firm's day-n value at w) + q_n(w) <= eps_n`.
State the inequality over all cube valuations if the existing market-maker lemmas
support that, otherwise over all worlds; say which and why.

**A1. Account ceiling.** For every `N` and every world live at `N`: `Q_N(W) <= U`.
(From the day inequalities and the firm's floor `-2`.)

**A2. Preservation.** If `Q_N(W) >= -B` for every `N` and every world live at `N`,
then no efficiently computable trader exploits `P` relative to `L`; if `P` is a
computable market it is a logical inductor over `L`. (From the day inequalities and
`trading_firm_dominance`.) Also the one-way converse: if some e.c. trader exploits
`P`, then `Q` is unbounded below over live prefixes.
*Do not* state that every e.c. trader's value is bounded; that is false. If you state a
quantitative bound, state it for a budgeted component of given firm weight.

**A3. Entailed conditions are free.** If every world live on day `n` satisfies every
day-`n` row, then `Q >= 0`, so A2 applies with `B = 0`. Instantiate at the deductive
region of `DeductiveRegion` to get: any `DualCertifiedMarket` whose regions are the
deductive regions is a logical inductor whose prices on each scheduled fragment lie
exactly in the hull of the currently plausible truth assignments.

**A4. The prefix reserve bound.** Fix `N` and a finite profile space. Let
`r_1 >= r_2 >= ... >= r_N >= 0` coordinatewise, total mass of `r_1` equal to 1, with
`r_n` supported on profiles of worlds live at day `n`, and
`sum_omega r_n(omega) g_{n,j}(omega) >= 0` for every row `j` of day `n`. Then for every
profile `omega` live at `N` with `r_N(omega) > 0`:
`Q_N(omega) >= -U (1 - r_N(omega)) / r_N(omega)`.
Proof route: `r_n · q_n >= 0`; summation by parts
`sum_n r_n·q_n = r_N·Q_N + sum_{n<N} (r_n - r_{n+1})·Q_n`; A1 on the supports.
Note the supports are the worlds live *at day n*, not at day `N`: with hindsight
supports the theorem is true but useless (one floor `W(phi) - c` on day 1 with `phi`
refuted on day 2 has no hindsight reserve, while the prefix reserve
`(c, 1-c)` then `(0, 1-c)` gives the right bound `U c/(1-c)`). Formalize that example
as the theorem's witness.
Corollary: a uniform lower bound on retainable reserve mass gives A2's hypothesis.
Relate to `OddsBankroll` if the relation is a short lemma; say so if it is not.

**A5. Obstruction.** For *any* history `P` with `P_n ∈ K_n` (no multipliers needed)
and any nonnegative staking `w_{n,j}`, the trader that sells `w_{n,j}` units of each
demanded bet has cumulative value `>= -Q^w_N(W)` in every world, where
`Q^w_N(W) = sum w_{n,j} g_{n,j}(W)`. Hence if `Q^w` is bounded above over live
prefixes and unbounded below, that trader's value is bounded below and unbounded
above; if it is an e.c. trader, it exploits `P`. State efficiency as a hypothesis on
the resulting trader.

**A6. Two counterexamples, as theorems about every compliant history.**
(a) One sentence `phi` both of whose values stay live forever; rows forcing
`P_n(phi) >= 1 - 2^-n`. Every demanded bet is nonnegative in the `phi`-true world, yet
selling one share a day has value `>= -1` where `phi` is true and `>= N - 1` where it is
false.
(b) Independent atoms `phi_n` with `D_n = {phi_1, ..., phi_{n-1}}`; rows forcing
`P_n(phi_n) >= 1 - 2 delta_n`, `delta_n = 2^{-n-2}`. Every demand is true and settles
the next day, yet selling `n` shares of `phi_n` on day `n` has value `>= -1` in every
live world and `>= N - 1` in a world live at `N`.
Use A5. If the trader's efficiency cannot be discharged against the pinned
dependency's definition in reasonable time, prove the value statements and leave
efficiency as a named hypothesis.

**A7. The conditional bridge (a lemma about sequences, then its instance).**
Sequence form: let `0 < c < 1`, `gamma > 0`, `x_n ∈ {0,1}`, `mu_n >= 0`, `U` real,
`Q_n = sum_{i<=n} mu_i (x_i - c)`, and suppose (ceiling) `Q_{n-1} + mu_n (1 - c) <= U`
for all `n`. Put `Y_n = U + 1 - Q_n` and `v_n = mu_n / Y_{n-1}`. Suppose (frequency)
that whenever `sum v_n` diverges, eventually
`sum_{i<=N} v_i x_i >= (c + gamma) sum_{i<=N} v_i`. Then `sum v_n` converges, `Y` is
bounded, `sum mu_n` converges, and `Q_n` minus any sub-sum is bounded below by
`-sum mu_n`.
Proof route: `Y_n = Y_{n-1} (1 - v_n (x_n - c))`, `Y_n >= 1`,
`log Y_N <= log Y_0 - sum v_n (x_n - c)`.
Instance: one fresh floor `W(phi_n) - c` per day with next-day settlement in a
`DualCertifiedMarket`; conclude A2's hypothesis. The frequency hypothesis is about the
realized normalized stakes; do not claim it follows from pseudorandomness against
efficient weightings — that implication is the open problem and is to be filed, not
proved.

**A8. Nonvacuity.** Inhabit the interface. The cheapest inhabitant should be the
unconstrained market with every multiplier zero and each region the whole cube, using
the existing market-maker bound; a second inhabitant with a nontrivial region and a
nonzero multiplier is wanted (a single sentence, a single floor, a hand-built finite
history is acceptable if the full construction of Tier B is not reached). Every
theorem registered must have its hypothesis package inhabited.

### Tier B — existence of an exactly compliant market (attempt after Tier A)

**B1.** For a day's continuous firm trade `t(p)` on a finite coordinate set and a
nonempty rational polytope `K` in the cube: for every `eps > 0` there is a rational
`p ∈ K` with `max_{y ∈ K} t(p)·(y - p) < eps`. (Projected fixed point of
`p ↦ proj_K(p + t(p))`, continuity, density of rational points.) Find how the pinned
dependency proves its market maker's fixed point and reuse that; do not prove Brouwer.

**B2.** From such a `p`: multipliers `mu_j >= 0` with
`t(p)·(w - p) + sum_j mu_j g_j(w) < eps` for every `w` in the cube. This is LP duality;
the Farkas lemma in `EconCSLib` is the expected tool.

**B3.** Assemble B1 and B2 day by day into a `DualCertifiedMarket` for any schedule of
nonempty rational polytopes. Existence first; computability of the resulting market is
a further step — attempt it only if existence closes, and otherwise file it.

If Tier B does not close, the report says exactly which lemma is missing and what was
tried, and the item is filed.

### Tier C — do not attempt; file only if Tier A shows them well-posed

The LP-exactness of the reserve bound for the class of all multiplier sequences under
the prefix ceilings; the volume bound `Q_N >= -sum H_n V_n eta_n` with a Hoffman
constant and minimum-norm multipliers; the finite-model equivalence (a constant
compliant pricing immune to bounded-risk unbounded-profit trading exists iff the
region meets the relative interior of the hull of the payoff profiles); the
settled-ledger almost-sure theorem under random observation; the extraction problem
(when `Q` is unbounded below, obtain an efficiently expressible normalized weighting).

## Standards particular to this round

- **Order.** A0–A3, then A5–A6, then A4, then A7, then A8 throughout, then Tier B.
  Depth over coverage: a closed A0–A6 with witnesses is a good round.
- **Lean discipline** as in `AGENTS.md`: sorry-free, `#print axioms` on everything,
  only the three allowed axioms, no `maxHeartbeats` changes. New modules go under
  `lean/Workspace/Normativity/Contrib/`.
- **Registry.** Register the headlines that close (A2, A3, A4, A5, the two parts of
  A6, A7, and Tier B if reached) in `projects/normativity/CLAIMS.md` in the same pull
  request, against items you file in `ATTENTION.md` within this scope. File at most
  four new items, one of which is the extraction problem. Names are provisional and
  listed in the report and the pull request.
- **Round records.** `state/rounds.json` with `depends_on`, the round directory under
  `projects/normativity/rounds/2026-11-10-exact-conditions-capital/` with a
  `THEOREM.md` in the style of
  `projects/normativity/rounds/2026-11-07-score-side-binding/THEOREM.md`
  (statement, hypotheses, inhabitants, what is typed, what is not shown), the
  provenance rows, and `prompts/2026-11-10-exact-conditions-capital/REPORT.md`.
- **Citations.** Attributions in the conversation behind this prompt (defensive
  forecasting, Blackwell, Walley, consistent price systems, a 2025 paper said to start
  from a propositionally coherent logical inductor) are unverified. Cite nothing you
  cannot verify; state mathematical content directly.
- **No wiki edits** beyond a claim-count binding a checker requires. Interpretation
  goes in the pull request description.
- **Site.** If `state/prs.json` / `state/concepts.json` plainly call for an entry by
  their contract, add it; if a judgment is needed, skip it and say so.

## Operating constraints on this machine

- Never call `lake` directly: `~/.claude/scripts/safe-lake.sh build <target>` from
  `lean/`. Run `~/.claude/scripts/resource-guard.sh check` before any long job, and
  `... wait` if it reports loaded. Other sessions are running.
- `tests/audit_axioms.py` (about 16 minutes) and `tests/run.py` (about 11 minutes)
  exceed the foreground command limit. Run each in the background with a long timeout
  and wait for it to finish before proceeding; do not end your run while a background
  job is still going.
- Commits are signed off (DCO) and carry `Model:` and `Prompt-author-model:` trailers;
  the pull request body carries the Model attribution section and the template's
  fields. Do not add co-author lines.
- Do not touch other worktrees under `.claude/worktrees/`.
- Before you exit, whatever state the round is in, write
  `/tmp/astra-consult/round/FINAL.md`: the pull request URL (or the branch and why
  there is no pull request), which of A0–A8 and B1–B3 closed with their declaration
  names, every statement that changed and how, what is unverified, and the gates' last
  results. Push the branch before writing it.
