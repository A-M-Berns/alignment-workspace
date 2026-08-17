# Funding, and whether the modified market is exploitable

The safety question is not whether the enforcement trader can lose money. It is
whether its losses buy ordinary traders unbounded plausible wealth, so that the
modified market is exploitable where the original was not.

## 1. Three quantities, and which one the criterion sees

**Enforcement intensity** `β_j` — a position size. It appears in the enforcement
inequality and in no accounting.

**Cumulative external credit** `F_T = ∑_{n ≤ T} worstloss(ζ_{E,n}, P_n)` — what
an outside funder would stand behind if the market demanded collateral. Finite at
every finite date by construction, with no uniform bound over dates.

**Enforcement liability** `B` *(provisional)* — the least bound with

    W( ∑_{i ≤ n} E_i(P) )  ≥  -B    for every date `n` and every `W ∈ PC(D_n)` .

Only the third is visible to the criterion, because `def:exploitation` assesses
net worth in worlds propositionally consistent with the stage. **The scarce
resource is not funding.** Logical Induction imposes no budget on traders at all
(`SOURCE_AUDIT.md` §2), so unbounded external credit is free; what is not free is
showing a loss in a world that is still plausible.

`F_T` and `B` come apart, and that gap is the round's central positive result.

## 2. Where a loss comes from

**Theorem 7 (liability identity).** At displayed prices `P` and in any world `W`,
the realised enforcement position is worth exactly

    ∑_j β_j g_j(P) · [ (⟪c_j, W⟫ - r_j) + g_j(P) ] .

*Proof.* Expand `⟪ζ_E(P), W - P⟫` row by row and substitute
`⟪c_j, P⟫ = r_j - g_j(P)` where `g_j(P) > 0`. ∎

Checked exactly on two thousand random instances,
`test_deduction.LiabilityIdentity`.

Read off the identity: a date costs the enforcement trader something only where a
**live violation** `g_j(P) > 0` and an **excluded world** `⟪c_j, W⟫ < r_j` meet on
the same row. Either factor alone is free, and both halves are exhibited.

**Theorem 8 (world-inclusive regions are liability-free).** If every
`W ∈ PC(D_n)` satisfies every row of `K_n`, then

    W( E_n(P) )  ≥  ∑_j β_j g_j(P)²  ≥  0    for every plausible `W` .

*Proof.* Theorem 2 with `x := W`. ∎

Kernel-checked as `pair_nonneg_of_mem`. No hypothesis about the market maker, the
ordinary traders, or the funding enters: it is a fact about the position and the
price. Since stages are nested, a world plausible at date `n` was plausible at
every earlier date, so the cumulative sum is a sum of nonnegative terms and
`B = 0`.

## 3. The safety theorem

The preservation result is two steps, and separating them matters because the
force layer must not appear to obtain a generalized criterion by quoting an
ordinary lemma about a construction it is not using.

**Step 1 — the generalized trading-firm theorem.** Under (L1)–(L3) of
`PAPER_RECONCILIATION.md` §2, `TF^live` dominates every efficiently computable
trader relative to the `L`-criterion: if some such trader exploits the market
relative to `L`, so does `TF^live`. This is `lem:tfdom` with `PC(D_t)` replaced
throughout, and it is **derived and unformalized** — the round's one load-bearing
step of that kind.

**Theorem 9 (enforcement preservation).** Let the modified algorithm be

    P_n := MarketMaker_n( TF^live_n(P_{<n}) + E_n , P_{<n} ) ,

and suppose

    inf over n and ω ∈ Ω_n^live  of  ω( ∑_{t≤n} E_t )  ≥  −B .

Then no efficiently computable trader exploits `P` relative to `Ω^live`, and every
such trader's assessed net worth is at most `1 + B`.

*Proof, composed.*
(i) The market maker's contract bounds the **combined** aggregate: for every world
and date, `ω(∑_{i≤n}(TF^live_i + E_i)) ≤ ∑_{i≤n} 2^{-i} < 1`. The `1` is the
source's geometric error budget and nothing else; a different per-date schedule
changes the constant and not the shape.
(ii) The enforcement trader contributes at least `−B` at every assessed world, by
hypothesis.
(iii) Subtracting, `ω(∑_{i≤n} TF^live_i) < 1 + B` for every date and assessed
world, so `TF^live`'s assessed values are bounded above and it does not exploit.
(iv) By Step 1, no efficiently computable trader exploits either. ∎

**Theorem 9 is conditional on Step 1.** The force layer supplies (ii) and nothing
else; it does not supply a generalized criterion on its own, and the living note
says so.

*(The deductive instance is the case `Ω^live = PC(D_t)`, where Step 1 is the
source's own `lem:tfdom` and Theorem 9 is unconditional.)*

**Corollary 10.** A region containing every assessed world gives `B = 0` and the
bound `1`. That is **sufficient for zero liability and not necessary for safety**:
§4 displays a trajectory excluding an assessed world at every date whose
cumulative liability is nonetheless bounded.

`test_safety.SafeCase` runs a four-date stage sequence with a world-inclusive
region and an ordinary aggregate positioned against the enforcement trader, and
computes liability `0` and bound `1` exactly.

**What Theorem 9 does not do.** It does not construct an exploiting trader when
`B` is unbounded; it loses a bound, which is a different thing. It is the one
step of the LIA capstone that the modification breaks, and re-establishing it is
the whole content of the safety claim.

## 4. The safety condition, below world-inclusiveness

The identity of Theorem 7 gives more than the `d ≡ 0` corollary the first pass
read off it. Rearranged, the enforcement position's value in a world `W` is at
least

    ∑_j β_j g_j(P)²  −  ∑_j β_j g_j(P) · d_j(W) ,

so the date's liability is at most the second sum, and **both factors are needed
on the same row**: a live violation, and a right-hand side that excludes `W`.
Kernel-checked as `weighted_square_sub_deficit_le_pair`, with an inhabitation
witness at a nonzero deficit.

**Theorem 11 is withdrawn.** It claimed the per-date liability ceiling is
`C_t · max_j d_j(W)`, independent of the intensity, on the reasoning that at
equilibrium the enforcement position offsets the ordinary one and so has size
`C_t` whatever the intensity.

That reasoning holds only where the contract forces the aggregate to vanish.
Positive market-maker slack does not force it: the contract bounds the
aggregate's cube maximum gain, and at an interior price that leaves room for
residual enforcement demand which nothing cancels. The counterexample has the
ordinary position at **zero**: `K = {P ≤ 1/2}`, `C = 1/100`, `ε = 1/8`,
`δ = 1/10`, so the prescribed intensity is `27/2`. At `P = 51/100` the violation
is `1/100`, the position is `27/200` short — thirteen and a half times the
declared volume bound — the contract holds at `1377/20000 ≤ 1/8`, conformance
holds, and the liability in the still-plausible world `W = 1` is `1323/20000`
against a claimed ceiling of `1/200`. `test_regressions.IntensityFreeCeilingIsFalse`
pins every one of those rationals.

**Theorem 11′ (the declared-quantity bound).** What survives, from the
kernel-checked identity by substituting the promised conformance `g_j ≤ δ_t` and
the prescribed intensity:

    L_t(W)  ≤  ∑_j β_j g_j(P_t) · d_j(W)  ≤  (ε_t + C_t) · ‖d_t(W)‖₁ / δ_t .

The intensity does **not** cancel, and the direction is the opposite of the
withdrawn claim: a tighter promised tolerance needs a larger intensity, which
permits a larger position, which raises the ceiling. **Conformance and liability
are traded against each other.** On the counterexample the pointwise form gives
`27/400` against an actual `1323/20000` — tight — and the declared form `27/40`.

**Corollary 12′ (the safety condition).** Bounded cumulative liability, and hence
the criterion, follows from

    ∑_t  (ε_t + C_t) · ‖d_t(W)‖₁ / δ_t  <  ∞    for every world plausible at every date.

A region containing every plausible world gives every deficit zero. That is one
way for the sum to converge and **not** the boundary.

### 4a. Expectation is not worldwise, and two bridges

The enforcement inequality bounds the position's value at price vectors in `K_t`.
An admitted credence's expectation is exactly that value at `π_t(μ)`, so what the
inequality delivers is

    E_μ[ E_t ]  ≥  ∑_j β_j g_j(P_t)²  ≥  0     for every μ ∈ C_t ,

and **nothing at any individual world**. Exhibited: under `K = {p(A) ≤ 1/2}` at
price `11/20` every admitted credence gives expectation at least zero — the
half-half credence gives `1/40` — while the live world `A = true` is worth
`−9/40` (`test_semantics.ExpectationIsNotWorldwise`).

Two sufficient bridges to a worldwise bound, and neither dominates.

**The deficit bridge**, which needs no support hypothesis and is what §4 already
gives: `L_t(ω) ≤ ∑_j β_j g_j(P_t) d_j(ω)`, valid at any world.

**The support bridge.** From `E_μ[X] ≥ a`, `μ(ω) ≥ θ` and an upper bound `U` on
`X` at the other worlds, `X(ω) ≥ (a − (1−θ)U)/θ`. With `a = 0` and `U` the
position's cube maximum gain — **named, not smuggled**, and computable from
declared quantities —

    E_t(ω)  ≥  − (1 − θ_t(ω)) · max_gain(ζ_{E,t}, P_t) / θ_t(ω) .

`θ_t(ω) = max { μ(ω) : μ ∈ C_t }` is the support capacity, computed exactly by
vertex enumeration. The bound degrades as the capacity shrinks, which is the
failure mode it exists to control: with `K = {p(A) ≤ c}` for `c` running `1/4`,
`1/20`, `1/100`, the expectation stays nonnegative while the worldwise loss grows
monotonically (`test_semantics.SmallSupportHidesLargeLoss`).

**Coverage is therefore a route, not a requirement.** The safety theorem consumes
bounded liability; the deficit bridge supplies it with no coverage hypothesis at
all. Quantitative support coverage is the alternative route, useful when the
deficits are not what is known. Nothing here shows either is necessary.

**Theorem 13 (a region excluding a live world at every date, enforced forever,
safely).** One sentence, settled true, so the sole plausible world is `W = 1`. A
source reserving against full certainty: `K_t = {P ≤ 1 − 2^{-t}}`, which excludes
`W` at every date. Ordinary volume `C_t = t`, market slack `2^{-(t+1)}`, promised
tolerance `1/10`.

Conformance holds at every date; the region is world-inclusive at no date; every
date shows a real plausible loss; and the cumulative liability is bounded, under
the corrected `12′`, by `10·∑_t t·2^{-t} + 10·∑_t 4^{-t}/2 = 20 + 5/3`. So the
criterion survives at every horizon. `test_contract.SafeWithoutWorldInclusiveness`
computes the whole trajectory exactly. **This result survives the retraction** —
the constant is larger and intensity-dependent; convergence is what the safety
theorem needs, and it converges. ∎

The contrast is the same construction with the depth held fixed: the bound
diverges (`test_contract.UnsafeWhenDepthDoesNotDecay`).

**The reading.** A constraint source may permanently exclude states deduction
permits — which is what a normative constraint is for — provided the depth of the
exclusion decays against the growth of ordinary trading volume. It is not
required to agree with deduction; it is required to *converge* on admitting what
stays live, at a rate. That is a substantive and checkable demand on a source,
and it is weaker than the one the first pass reported.

**What it does not say.** That the condition is necessary; that `12′` is the
tightest ceiling; or that a source producing normative content can meet it. The
first is item 40, the third is item 39. And it says nothing about *which* worlds
the sum ranges over — `PAPER_RECONCILIATION.md` §5 shows that reading the
assessment set off the constraint makes the whole condition vacuous.

## 5. Necessity: how much converse survives

**Not the general converse.** The proof of Theorem 9 runs one way only, and there
is a structural reason. In this framework traders do not trade with each other: a
trader's net worth is a function of its own positions and the price path, and the
enforcement trader's losses fund nobody. `test_safety.SubsidyHarvesting` shows
this directly — varying the enforcement position across `{-3, 0, 50}` with the
price path held fixed leaves an ordinary trader's net worth unchanged. So
"harvesting the subsidy" in the direct sense does not exist here, and a converse
would have to run entirely through the price channel.

**A converse in a persistent one-sided case, by witness.** Take one sentence,
`φ` settled true from some date on, a source demanding `p(φ) ≤ 1/2`, and an
ordinary aggregate of mass `1/2` buying `φ`. Then:

| intensity | enforced price | violation | enforcement value per date, plausible world |
|---|---|---|---|
| `10` | `11/20` | `1/20` | `-9/40` |
| `100` | `101/200` | `1/200` | `-99/400` |
| `1000` | `1001/2000` | `1/2000` | `-999/4000` |

Sharper enforcement rises here towards `M · d(W) = 1/4`, which is a fact about
this fixture and **not** a general ceiling — see the retraction in §4. Over eight dates the enforcement liability is `9/5`, so
Theorem 9's bound would be `1 + 9/5 = 14/5`; the trader that buys one share of
`φ` on each date it has verified `φ` settled has plausible net worth `18/5`,
bounded below by zero and growing linearly. It exploits.
`test_safety.SupportCoverageFailure` computes every number in that paragraph
exactly.

What makes this shape unsafe is not that the region excludes a live world. It is
that the exclusion **persists at a fixed depth while the ordinary volume grows**,
so `∑_t C_t · d_t(W)` diverges. §4 gives the general condition and a region that
excludes a live world at every date and is safe anyway.

## 6. Where the converse is known to fail

**Weak enforcement is free.** At `β = 1` in
the same fixture the enforced price is `1` — enforcement has failed entirely — and
the enforcement liability is exactly zero. So bounded liability does not imply
world-inclusivity; it implies the enforcement trader was never made to hold a
position against a plausible world. Bounded liability and world-inclusivity are
therefore not equivalent, and the round claims no equivalence.

## 7. Liability laundering does not work

Moving the enforcement position onto fresh coordinates each date keeps every
single-date exposure at a constant `9/40` while the cumulative plausible loss
grows linearly: `27/20` over six dates, `27/10` over twelve, `27/5` over
twenty-four (`test_safety.LiabilityLaundering`). The reason the round's condition
catches this is that it is stated on `∑_{i≤n} E_i` assessed in **one** world, not
on a per-date bound. A per-date liability bound would pass every one of those
dates and miss the divergence.

The same fixture is the funding trajectory the model asks for: credit finite at
each date, unbounded over dates, with the per-date draw constant
(`test_safety.FundingTrajectory`).

## 8. What is settled and what is not

Settled: bounded enforcement liability is sufficient for the criterion, with an
explicit bound; the identity that says exactly where a liability comes from and
that both its factors are needed; the declared-quantity bound `11′` and the
summability condition `12′`; a region that excludes a live world at every date and
is safe anyway; a world-inclusive presentation as the `d ≡ 0` special case of
that; and a worked case where a fixed-depth exclusion against growing volume
produces a real exploiting trader.

Withdrawn: the intensity-free ceiling `C_t · max_j d_j(W)`, with its
counterexample kept as a regression.

Not settled: whether unbounded enforcement liability *always* produces an
exploiting efficiently computable trader. **[conjecture]** it does when the
excluded plausible world persists and the exclusion is detectable within the
efficiency bound, which is what the witness instantiates. Nothing here proves the
general case, and the round does not assume it.

Not settled: whether the modified algorithm remains a *computable* belief
sequence for every effectively presented region. Argued in `MODEL.md` §5,
not proved.
