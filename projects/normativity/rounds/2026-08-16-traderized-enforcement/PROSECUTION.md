# Prosecution

Sixteen attacks. Four land, one lands partially, and the rest are answered. The
four that land are in the report and in the pull-request description.

## W1 — Fake enforcement: the trader profits but the price does not move

**Answered, and sharpened by the exactness fork.** For a region with an interior
the answer is now outright: the interior-anchored compiler forces membership
against every disturbance in the declared class, so nothing survives outside.
For a region without an interior no continuous trader does, and what is delivered
instead is a declared tolerance — which the constitutional interface is built to
consume. The old answer follows.

**Answered.** The profit and the price constraint are the same inequality. At a
contract-satisfying price, `∑_j β_j g_j² ≤ ε_n + M_n` (Theorem 4), so a violation
that survives is a violation the contract has paid for out of the slack and the
opposing volume. At slack zero with no opposing volume the sum is zero and the
price is inside (Theorem 3, kernel-checked). What fails is a *different* thing —
a trader that profits from a violation without the market maker pricing against
it, which is W3.

## W2 — Infinite-money equivocation

**Answered, and the premise is inverted.** No step assumes same-date infinite
purchasing power; the realised position is `ζ_E(P) = ∑_j β_j g_j(P) c_j`, a finite
rational vector at every date, and its worst-case single-date loss is recorded per
date in `funding.FundingLedger`. The inversion: the framework imposes no budget on
traders at all (`SOURCE_AUDIT.md` §2), so *growing external credit is not the
scarce thing*. Plausible-world loss is. A proof that leaned on unbounded credit
would be leaning on something free and irrelevant.

## W3 — Wrong payoff translation, and the naive separator

**Lands against the naive construction; that is why the round does not use it.**
A single separating hyperplane compiles to a legal trade but enforces only its own
half-space, and the market maker's response is to pin the price at a cube extreme
in the direction of net demand — which generally leaves the region by another
row. On `K = [1/2, 3/4]` the single-separator trader admits `{5/6, 11/12, 1}`,
all outside `K`; the full row system rejects every one of them
(`test_enforcement.NaiveConstructionFails`).

The payoff translation itself is checked rather than asserted: at `P = 1/4` with
`K = [1/2, 3/4]` and `β = 2` the position is `1/2` share long, costs `1/8` at the
displayed price, pays at most `3/8` and loses at most `1/8`
(`test_enforcement.SeparatingPortfolio`).

## W4 — β/funding conflation

**Answered, with the strongest available separation.** In the adversarial fixture
the realised position is exactly `-1/2` for `β ∈ {10, 100, 1000}` — identical —
while the violation falls as `1/20, 1/200, 1/2000`
(`test_safety.IntensityIsNotFunding`). Position size is set by the opposing
volume; intensity sets precision. Under an exact contract intensity does not even
do that: the contract-feasible set is identical across `β ∈ {1/100, 1, 37}`.

## W5 — Subsidy arbitrage: an ordinary trader farms the losses

**Lands, but not in the form stated, and the real form is the round's main
negative.** There is no direct channel: a trader's net worth is a function of its
own positions and the price path, and varying the enforcement position with prices
held fixed changes nothing for it (`test_safety.SubsidyHarvesting`). The real
channel is the price. In the persistent-exclusion fixture the ordinary trader's
gain per date *equals* the enforcement trader's loss per date, both `9/40`, and
over eight dates its plausible net worth reaches `18/5` against the safety
theorem's bound of `14/5`. It exploits. `FUNDING_AND_SAFETY.md` §4.

## W6 — Tiny-support world: losses hidden where every admissible valuation prices
near zero

**Answered.** The attack presumes losses are assessed under a measure that can be
made small. They are not: `def:exploitation` assesses net worth **worldwise**, at
each plausible world separately, with no weighting. A world that is still
plausible counts at full strength however unlikely the region's points make it.
The liability identity (Theorem 7) has no measure in it, and the world-inclusive
condition quantifies over `PC(D_n)` pointwise.

## W7 — Liability laundering into fresh coordinates

**Answered by the shape of the condition.** Rotating the position through three
coordinates keeps every single-date exposure at `9/40` while the cumulative
plausible loss grows linearly — `27/20`, `27/10`, `27/5` over six, twelve and
twenty-four dates (`test_safety.LiabilityLaundering`). The round's condition is
stated on `∑_{i≤n} E_i` assessed in **one** world, not per date, so it sees the
divergence. A per-date liability bound would have passed every one of those dates.

## W8 — Settlement/enforcement conflation

**Answered, and the distinction is a test.** Enforcement supplies the settlement
interface's third column and neither of the other two. It writes no report — the
plausible set is unchanged by taking a position — and it leaves no residue: a
region demanding `p(φ) ≥ 1` fixes the price at that date, and with the row
withdrawn the next date's price is free again. A settlement cannot be withdrawn,
so the coherence polytope stays cut and mispricing stays exploitable
(`test_deduction.SettlementIsNotEnforcement`; `DEDUCTION_SPECIAL_CASE.md` §5).

## W9 — Deduction non-equivalence

**Lands, and is reported as a finding rather than defended against.** The
traderized process does not do what `D` does. `D` is ineliminable from the
criterion, because exploitation is *defined* over `PC(D_n)`; and from the
construction, because a `D`-free budgeter loses `lem:budgeter`.3 and with it
trading-firm dominance (`SOURCE_AUDIT.md` §3). Traderized enforcement of the
coherence polytope *adds* a finite-date guarantee; it replaces nothing. The four
candidate equivalence relations are stated and each is answered separately
(`DEDUCTION_SPECIAL_CASE.md` §6); two are false.

## W10 — Criterion breakage

**Answered conditionally, and the condition is exactly the interesting one.**
Theorem 9 re-establishes the criterion under bounded enforcement liability, and
Corollary 10 gives liability zero for world-inclusive regions. Without that
hypothesis the criterion is not merely unproved — W5's fixture breaks it. The step
that breaks is localized to one lemma application,
`liaTrader_not_exploited` (`Construction/LIA.lean:96`).

## W11a — Exactness bought at the safety property's expense

**Lands, and it is the follow-up's sharpest finding.** The compiler that achieves
exact enforcement does not vanish on the region: inside the collar it holds a
position against no violation at all. So the enforcement inequality's
nonnegativity reading does not apply to it, and on a world-inclusive region where
the violation-proportional position never loses in a plausible world, the
interior-anchored one is worth `-1/2` — at a price **inside** the region with
every row violation zero (`test_exactness.ExactnessCostsSafety`).

The two compilers are therefore not ordered. One is safe and approximate; the
other is exact and unsafe. Nothing in the round produces one that is both, and
whether such a thing exists is open.

## W11 — Trivial constraint: the region hard-codes the answer

**Lands as a limitation on what the mechanism means, not on whether it works.**
The theorem holds when `K_n` is a singleton and then forces the price to that
point exactly — which shows the mechanism does not smuggle in an answer, and also
shows it is a *complete* steering channel for whoever writes the rows. Both
readings are true and the second is the more important one
(`README.md`, relation to Legitimacy). Non-triviality is checked where it matters:
on the Boolean fragment the enforced region contains many grid points
(`test_deduction.SupportPresentation`), and before a sentence is settled
enforcement leaves its whole feasible segment free
(`test_deduction.TraderizedDeduction`).

## W12 — Noncomputable enforcement

**Lands as a cost, and the cost is stated.** The compiler needs a rational row
system computable at date `n`. For deduction that means the facet system of
`conv(PC(D_n))`, whose vertex set is up to `2^{|Φ_n|}` — computable, not
efficiently computable, and consistent with the `#P`-hardness of arbitrage-free
pricing under a subsidy bound in combinatorial markets. The exemption that makes
this legal is that the enforcement trader sits in the price-setting aggregate
rather than in the criterion's quantifier, where only computability is required
(`DEDUCTION_SPECIAL_CASE.md` §4).

A source that supplies a *set* with no presentation supplies nothing the compiler
can consume, and the round says so rather than assuming an oracle.

## W13 — Time-varying escape: the region moves and the trader chases

**Answered, with a split, and the split is now quantitative.** Every enforcement
statement is per date and consumes no stability whatever: Theorems 2, 3 and 4
hold at each date independently, so `K_n` may vary arbitrarily. The *safety*
statements do not, and the follow-up says exactly how much variation they need:
`∑_t C_t · max_j d_j(W) < ∞`. A region that moves is safe when it moves *towards*
admitting the worlds that stay live, fast enough to beat the growth in ordinary
volume, and unsafe when it holds a fixed exclusion. Both are displayed
(`test_contract`). Time-variation is not the enemy; a non-decaying exclusion is.

## W14 — Vocabulary collision

**Answered by construction and listed.** Four live collisions —
`coverage(Due)`, answerability liabilities, deference authority, the settlement
interface's downside limit — each with the reason the objects differ, in
`INTEGRATION_MAP.md` §3. The round introduces no unqualified `coverage`,
`liability` or `authority trader`, and proposes no identification.

## W15 — Normativity overclaim: force described as legitimacy

**Answered by a stated separation.** Operative force is cheap: any nonempty
region with a computable rational row presentation gets it, at any positive
intensity. The mechanism is indifferent to whether the region is right, and W11
shows it will hold a singleton just as readily. The one thing the market itself
checks about a source is deductive consistency — a source that persistently
excludes a settled fact makes the market exploitable (W5's fixture) — and that is
not legitimacy. `README.md` states the separation and the report repeats it.

## W16 — Deduction overclaim: a toy arbitrage described as replacing `D`

**Answered.** The finite fixtures are labelled `test-supported` and the
composition they illustrate is labelled `derived`; no outcome theorem about the
modified algorithm is claimed beyond Theorem 9, whose hypotheses are named. The
claim that would be an overclaim is refused explicitly in W9.

## W17 — The force mechanism escapes attribution by naming a disturbance bound

**Answered, and this reverses the first pass's own finding.** The earlier reading
was that `∑_j β_j g_j² ≤ ε_t + C_t` makes ordinary traders partly responsible for
a violation, which would break `NL-SI-T4`'s total-and-exclusive attribution.

`C_t` is a *declared assumption*, not a suffered cause, and the trading-firm
construction computes a bound on its own volume from the belief history — so the
mechanism can name it before the price is set. Realised volume within `C_t` and a
price outside `δ_t` is the implementation's failure; realised volume above `C_t`
is a false declaration, detectable after the fact; a conforming price the docket
still cannot certify is the tolerance being sound and not working, which is `T1`'s
existing distinction. Three cases, one respondent each.
`FORCE_INTERFACE.md` §4.

## What lands

W3 against the naive construction, which is why the round uses the full row
system. W5 in its price-channel form. W9, which downgrades the deduction claim
from replacement to addition. W12, which prices the deduction case honestly.
**W11a, which is the follow-up's own worst finding: exactness and safety are
bought from the same account.** W11 lands partially, as a fact about what the
mechanism means rather than whether it holds. W17 was raised by the first pass
and is withdrawn by the second.
