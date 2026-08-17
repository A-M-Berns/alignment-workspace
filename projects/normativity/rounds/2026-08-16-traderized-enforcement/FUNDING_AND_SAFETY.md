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

**Theorem 9 (sufficiency).** Let the modified algorithm be

    P_n := MarketMaker_n( TradingFirm^D_n(P_{<n}) + E_n , P_{<n} ) .

If the enforcement liability is bounded by some finite `B`, then no efficiently
computable trader exploits `P`, and every such trader's plausible net worth is at
most `1 + B`.

*Proof.* The market-maker lemma applies to the priced aggregate, so
`W(∑_{i≤n}(TF_i + E_i)) < 1` for every world and date. Subtracting,
`W(∑_{i≤n} TF_i) < 1 + B` for every date and plausible world, so `TradingFirm`'s
plausible assessments are bounded above and it does not exploit. Trading-firm
dominance is untouched by the modification — it relates `TradingFirm`'s plausible
net worth to a component's, given the market — so no efficiently computable
trader exploits either. ∎

**Corollary 10.** A world-inclusive presentation gives `B = 0` and the bound `1`,
which is the unmodified market's own bound. Enforcement onto such a region costs
the criterion nothing.

`test_safety.SafeCase` runs a four-date stage sequence with a world-inclusive
region and an ordinary aggregate positioned against the enforcement trader, and
computes liability `0` and bound `1` exactly.

**What Theorem 9 does not do.** It does not construct an exploiting trader when
`B` is unbounded; it loses a bound, which is a different thing. It is the one
step of the LIA capstone that the modification breaks, and re-establishing it is
the whole content of the safety claim.

## 4. Necessity: how much converse survives

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

Sharper enforcement costs strictly more, converging on `M · dist(K, W)`. Over
eight dates the enforcement liability is `9/5`, so Theorem 9's bound would be
`1 + 9/5 = 14/5`; the trader that buys one share of `φ` on each date it has
verified `φ` settled has plausible net worth `18/5`, bounded below by zero and
growing linearly. It exploits. `test_safety.SupportCoverageFailure` computes
every number in that paragraph exactly.

So in this shape the failure of world-inclusivity is not merely a lost bound: it
is an actual exploitation, by a trader whose construction is explicit. That is
one direction of the necessity question answered by a witness, not a theorem —
the witness fixes `K`, the opposing volume, and the persistence of the settled
fact, and none of those is shown to be removable.

**Where the converse is known to fail.** Weak enforcement is free. At `β = 1` in
the same fixture the enforced price is `1` — enforcement has failed entirely — and
the enforcement liability is exactly zero. So bounded liability does not imply
world-inclusivity; it implies the enforcement trader was never made to hold a
position against a plausible world. Bounded liability and world-inclusivity are
therefore not equivalent, and the round claims no equivalence.

## 5. Liability laundering does not work

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

## 6. What is settled and what is not

Settled: bounded enforcement liability is sufficient for the criterion, with an
explicit bound; a world-inclusive presentation gives liability zero
unconditionally; the identity that says exactly where a liability comes from; and
a worked case where losing world-inclusivity produces a real exploiting trader.

Not settled: whether unbounded enforcement liability *always* produces an
exploiting efficiently computable trader. **[conjecture]** it does when the
excluded plausible world persists and the exclusion is detectable within the
efficiency bound, which is what the witness instantiates. Nothing here proves the
general case, and the round does not assume it.

Not settled: whether the modified algorithm remains a *computable* belief
sequence for every effectively presented region. Argued in `MODEL.md` §5,
not proved.
