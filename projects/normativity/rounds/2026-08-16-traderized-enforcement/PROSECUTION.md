# Prosecution

Twenty-two attacks — sixteen from the opening dispatch and six raised by later
passes, three of those against the round's own claims. The current verdict is at
the foot of the file; two earlier verdicts are withdrawn there.

## W1 — Fake enforcement: the trader profits but the price does not move

**Answered, and sharpened by the exactness case analysis.** In the dimensions
tested, an interior-anchored compiler on a region with an interior forces
membership against every disturbance in the declared class, so nothing survives
outside — `test-supported`, not general. For a one-sentence region strictly
inside `(0,1)` no continuous trader does, which is derived. What is delivered in
that case is a declared tolerance, which the constitutional interface is built to
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
statements do not. What they need is bounded cumulative enforcement liability,
for which the surviving sufficient bound is
`∑_t (ε_t + C_t)·‖d_t(ω)‖₁ / δ_t < ∞` — intensity-dependent, since the
intensity-free ceiling was withdrawn (W18). A region that moves is safe when it
moves *towards* admitting the worlds that stay live fast enough for that sum to
converge, and the fixed-exclusion case makes it diverge. Both are displayed
(`test_contract`). Time-variation is not the enemy; a non-decaying exclusion
against growing volume is.

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
shows it will hold a singleton just as readily.

An earlier draft added that the market "checks deductive consistency" of a
source. **Withdrawn as an overclaim.** The market checks its own price contract.
What is true is that a source generating unbounded cumulative enforcement
liability breaks the preservation theorem's hypothesis, and that in one displayed
shape an explicit trader exploits (W5). That is a witness, not a soundness check,
and neither is legitimacy.

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

## W18 — The liability ceiling assumed the aggregate vanishes

**Lands, and the claim is withdrawn.** The second pass asserted an
intensity-free ceiling `C_t · max_j d_j(W)`, reasoning that the enforcement
position offsets the ordinary one at equilibrium. Positive market-maker slack
does not force the aggregate to vanish, so there is residual enforcement demand
nothing cancels. With the ordinary position at **zero**, a declared volume bound
of `1/100`, slack `1/8` and tolerance `1/10`, the prescribed intensity is `27/2`,
the position at `P = 51/100` is `27/200` short, and the liability is `1323/20000`
against a claimed ceiling of `1/200`. Contract and conformance both hold.
`test_regressions.IntensityFreeCeilingIsFalse`.

What replaces it carries the intensity, and reverses the direction: a tighter
promised tolerance raises the ceiling.

## W19 — Empty interior was read as impossibility

**Lands, and the generalization is withdrawn.** The proved theorem hypothesises a
one-sentence region strictly inside `(0,1)`; the prose applied it to every region
with empty interior, and drew from that the conclusion that settlement equalities
are unenforceable. `K = {0}` is enforced exactly by the constant strategy
`ζ_E ≡ −λ` for any `λ > C`: a short position at a zero price costs the
disturbance nothing to leave, so the contract charges zero there and `(λ−C)P > 0`
everywhere else. Settlement pinning is the **easy** case.
`test_regressions.EmptyInteriorDoesNotImplyImpossibility`.

The case the generalization got right is isolated and kept: a coherence relation
cuts a segment meeting the open cube, in no proper face, and a cancellable band of
half-width `C/(2β)` survives every intensity.

## W20 — The generalized assessment set can be chosen to satisfy the safety condition

**Raised, then withdrawn twice over.** The attack was that live worlds derived
from the constraint make the liability identically zero. It rested on reading a
live world as one whose own price vector is admissible, which is not the
definition; under support the disfavoured world stays live and the position still
loses there.

What survives is much narrower and is `PRIORITIES.md` item 44: a constraint can
set a world's support capacity to **zero**, and then that world genuinely leaves
the assessment set. That act is what a settlement performs, so the question is
whether the settlement interface's write-once and no-claw-back clauses bind it.
`test_semantics.CapacityComesFromTheSemanticSet` and
`test_regressions.DiracLiveWorldsAreNotLiveWorlds`.

## W21 — Price-space membership read back as semantic admissibility

**Lands, and it is the pass's own finding.** Defining the semantics as
`π⁻¹(K_t)` is not a derivation from `K_t`; it is the largest lift consistent with
it. With deduction admitting only `{00, 11}`, the projection is `{p_A = p_B}` and
the preimage makes **all four** worlds live — including two whose entire
combination is deductively impossible. Deductive recovery fails outright under
that reading.

The repair is to make `C_t` primitive and `K_t = π_t(C_t)` its image, and to name
the reverse direction a lift wherever a source supplies only a region.
`test_semantics.ProjectionLosesSupport`.

## Current verdict

### Landed criticisms

**W3** — a single separating hyperplane enforces one half-space and overshoots;
the round uses the full row system.
**W5** — the price channel is a real transfer route, and a source can make
ordinary traders unboundedly rich through it.
**W9** — the traderized process does not do what `D` does; deduction is recovered,
not replaced.
**W11a** — exactness and safety are bought from the same account, and the round
produces no compiler that is both.
**W12** — enforcing coherence exactly is computable and not efficiently so.
**W18, W19, W21** — the round's own three counterexamples, each retracting a claim
it had made.

### Withdrawn criticisms

**W17** — the disturbance bound was read as an unattributable third cause; it is a
declared assumption, and attribution stays total and exclusive.
**W20** — the generalized assessment set was said to launder liability
automatically. It rested on the Dirac reading of a live world, which is not the
definition; under support the disfavoured world stays live and the position still
loses there.

### Remaining open attacks

**Is either liability bridge necessary?** (item 45). **What governs removing a
world from support altogether?** (item 44) — settlement-shaped, and the narrow
residue of W20. **Does a compiler exist that is both exact and safe?** (item 43).
**Is face-solidity the right exactness condition?** — conjectural, with witnesses
on both sides.

### The exactness picture, at its earned levels

Exactness at zero slack against the violation-proportional compiler is
kernel-checked. The interior-anchored construction is test-supported in one and
two dimensions. Impossibility for a one-sentence region strictly inside `(0,1)`
is derived. Cube-face settlement pinning is enforced exactly, witnessed in one and
two dimensions — **it is the easy case, not the hard one**. The general
`face-solidity` condition is a conjecture. No claim is made that every
empty-interior region is hard.


## Attacks 23–28: the outflow account

**23. Charge each endorsement separately.** *Lands.* Finite per-endorsement caps
do not sum. One endorsement live per date, each spending `2` and then retiring,
gives `2n` after `n` dates while obeying finite gating everywhere. The clause must
be global or summably allocated. `test_outflow.PerEndorsementCapsDoNotAggregate`.

**24. Let finite gating carry the lifetime bound.** *Lands.* Gating bounds rows
per date and says nothing about the number of dates.
`test_outflow.GatingIsNotALifetimeBound`.

**25. Buy stronger force by restating the rows.** *Lands, and the first verdict
here was wrong.* The refutation divided the intensity by the row count; the
installed `ForceDeclaration` does not, so the refutation was about a compiler
nobody calls. Under the installed one, `k` duplicates scale position and charge by
`k`, rescaling by `λ` scales them by `λ²`, and a redundant non-duplicate row
changes the emitted force while leaving the admissible set fixed. Only rescaling
is neutral at a matched actual conformance target.
`test_outflow.PresentationChangesTheInstalledCompiler`, `PRIORITIES.md` item 46.

**26. Answer exhaustion by weakening the core minimum.** *Fails to help.* The
worst deficit `max(0, r − m_c)` contains no `θ`, so the charge is unchanged. The
exhaustion behaviour that looks cheapest buys nothing.

**27. Spend a fixed share of the remaining account, and never exhaust it.**
*Lands against the policy, not against the account.* Proportional spending really
does never run out — `R_t = R_0(1−ρ)^t` — and the tolerance it affords diverges,
so force goes vacuous anyway. Never exhausting is not keeping force available,
and `meaningful_dates_are_finite` shows no protocol does better.

**28. Replenish the account from outside.** *Lands, and is the one to watch.*
Unbounded replenishment destroys the guarantee outright, and it is precisely the
failure `NL-SI-P1` names — an outside source replenishing every paid loss while
only current positions are tracked. Any implementation must bound replenishment
globally or confine it to a new era with its own finite allocation.


## Attacks 29–33: the cost product

**29. Persistent normative distance exhausts any account.** *Fails, and this round
asserted it.* The argument dropped the `(ε_t + C_t)` factor: `δ_t ≤ 1` gives
`q_t ≥ (ε_t + C_t)D_t`, not `q_t ≥ D_t`. With pressure `2^-t`, a depth fixed at
`1/2` at tolerance `1` sums to under `1` forever.
`test_outflow.DepthOnlyImpossibilityIsWithdrawn`.

**30. Then nothing bounds the account.** *Fails.* Floors on depth **and** pressure
with a ceiling on tolerance bound the funded dates by `B·δ̄/(cd)`. All three are
load-bearing and `positive_floor_dates` refuses without them.

**31. Pay the account with deficits you like.** *Landed, now closed.* `charge`
took an arbitrary list. It now takes a `LiveDeficitCertificate` that records how
the aggregate was established, and `raw_charge` — the uncertified arithmetic — says
in its own docstring that paying with it proves nothing about any world.

**32. Emit force without paying.** *Landed, now closed.* `compile_force` returns a
conformance certificate and nothing stopped a caller reading it as a safety one.
`compile_funded_force` pays before constructing the position and returns a
distinct type; the unaffordable path cannot produce a certificate at all.

**33. Refill the account.** *Landed, now closed.* There is no `add_capital`.
`replenish` is bounded by a lifetime ceiling declared at construction and refuses
by default, because the bound a caller may quote is the ceiling rather than the
initial capital.


## Attacks 34–39: laundering the hypothesis through the API

**34. Certify an easy region, enforce a hard one.** *Landed, now closed.* A
`verified` certificate for `p ≥ 0` has aggregate zero honestly. Paid against
`p ≥ ½` it charged nothing while the emitted position lost at a live world.
Certificates now carry the exact row presentation, and `compile_safe_force`
computes the deficit from the region it enforces.
`test_outflow.CertificateSubstitution`.

**35. Certify a duplicated presentation, enforce the deduplicated one.**
*Landed, now closed.* Duplicates change the emitted position, so they change the
identity, and the presentation key preserves them.

**36. Permute the sentence coordinates.** *Landed, now closed.* The world vectors
are unchanged and what they mean is not; the support key is part of the binding.

**37. Reuse a later certificate earlier.** *Landed, now closed.* Live sets shrink,
so a later aggregate is smaller — on the displayed instance, zero against `1/2`.
Date and live-world set are both bound.

**38. Fill in `verified=True`.** *Landed, now closed.* The initializer requires a
module-private witness; asserted bounds are a separate type that cannot reach the
safety-certified path at all.

**39. Ask for loose force and be given tight force.** *Landed, now closed.* The
relax policy bought the tightest tolerance the allowance could afford, so a
request for `1/2` against an account affording `1/10` got force five times
stronger than asked for and spent the whole allowance. Relaxation now moves
tolerance in one direction only. `test_outflow.RelaxOnlyLoosens`.


## Attacks 40–41: the last two mismatches

**40. Certify a narrow assessment, enforce against a wide one.** *Landed, now
closed.* With date, support and row presentation all held fixed, `binds` still
accepted a certificate computed against a different live set. `{A = 1}` has
aggregate `0` where `{A = 0, A = 1}` has `1/2`, so the wide request was funded for
nothing. All four identities are now checked, and the lower-level entry point
takes the live worlds precisely so that it can check the fourth.
`test_outflow.CertificateSubstitution.test_a_certificate_from_another_assessment_cannot_fund_this_request`.

**41. Reorder the rows.** *Fails, and the round had claimed it landed.* The
compiled position and the certified aggregate are both sums over rows at uniform
intensity, so permutation permutes summands and moves nothing — verified across
all six permutations of a three-row system. The presentation key now canonicalizes
order and keeps multiplicity. The prose saying row order changes force was wrong.
`test_outflow.RowPermutationIsInvariant`.
