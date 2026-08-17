# Deduction as a constraint source

The generality claim is worth little if ordinary deduction does not fit. It fits,
and fitting it is what shows where the interesting boundary is.

## 1. Which constraint deduction supplies

At date `n` the deductive stage `D_n` determines `PC(D_n)`, and the price vectors
some credal state over those worlds reproduces are exactly the **coherence
polytope** `conv(PC(D_n)|_Φ)`. Enforcing membership in it is enforcing the
finite-date form of what Logical Induction otherwise obtains only in the limit
(`thm:lc`).

`conv(PC(D_n))` is world-inclusive by definition: it contains every plausible
world as a vertex. So by Corollary 10 of `FUNDING_AND_SAFETY.md`, enforcement
onto it has enforcement liability zero, and by Theorem 9 the modified market
satisfies the criterion with the unmodified bound. **Traderized deduction needs
no subsidy.**

Verified across a stage sequence in `test_deduction.TraderizedDeduction`: at
slack zero every contract-feasible price is in the convex hull of the plausible
worlds, checked by exact convex-hull membership rather than by the row system
that produced it; and the realised enforcement position is worth at least zero in
every plausible world at every grid price.

## 2. Can deduction be enforced by ordinary bounded-downside traders?

Better than that: by Theorem 8 the enforcement position for a world-inclusive
region is worth at least **zero** in every plausible world, not merely bounded
below. It is not a bounded-downside trader with a large budget; on the plausible
set it never loses.

So the enforcement trader is not a generalisation of ordinary deductive trading
by being richer. It is a generalisation in exactly three respects, none of them
financial (`SOURCE_AUDIT.md` §7): unit weight rather than `2^{-k-b}`, no budget
cap, and no efficient-computability requirement. `TradingFirm` already contains
every efficiently computable trader, so an efficiently computable coherence
arbitrageur is *already* in the priced aggregate — at weight `2^{-k-b}`, which by
Theorem 4 buys a violation bound of `sqrt((ε_n + M_n) 2^{k+b})` and therefore
nothing useful at a finite date. The privilege is what converts an existing
asymptotic pressure into a finite-date bound.

## 3. Presentation matters, and the cheap presentation is not enough

Deduction supplies a *set*; the compiler needs *rows*. Two presentations, and the
gap between them is real.

The **affine-relation presentation** takes the equalities every plausible world
satisfies — `p(φ) + p(¬φ) = 1` and the like. On the fragment `{φ, ψ, φ∧ψ, φ∨ψ}`
it admits 24 of the 256 grid points at denominator three that are **not**
coherent, among them `(0, 1/3, 1/3, 0)`, which prices the conjunction above one
of its conjuncts. No affine relation among the priced sentences rules that out;
`p(φ∧ψ) ≤ p(φ)` is a genuine inequality facet.

The **support-function presentation** of `MODEL.md` §4 at coefficient bound one
cuts out the coherence polytope exactly on that fragment's grid — verified point
by point against exact convex-hull membership,
`test_deduction.SupportPresentation`.

So "traderize deduction" is not one construction. Enforcing the affine relations
is cheap and enforces strictly less than coherence; enforcing coherence needs the
facet system.

## 4. What the facet system costs

The coherence polytope's facets are not free. The support-function presentation's
row count grows fast in the coefficient bound — 80 rows at bound one on a
four-sentence fragment, 624 at bound two — and in general the vertex set is
`PC(D_n)` restricted to the fragment, of size up to `2^{|Φ_n|}`. Enforcing
coherence exactly is therefore computable but not efficiently computable, which
is consistent with the neighbouring result that arbitrage-free pricing under a
subsidy bound is `#P`-hard in the worst case for combinatorial markets
(`SOURCE_AUDIT.md` §8).

This is a real limitation on the architecture and not a footnote: the mechanism
that makes deduction operative at a finite date is exactly as expensive as
deciding coherence on the priced fragment.

## 5. What traderization does not supply

The settlement interface separates three things a world-channel provides:
**reports**, **timing**, and **enforcement**
(`projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §0).
Traderization supplies the third and neither of the others.

**No reports.** The enforcement trader writes nothing into the record. Its entire
effect at a date is a coefficient vector; the payout function is the world, which
it does not touch. `test_deduction.SettlementIsNotEnforcement` checks that the
plausible set is unchanged by taking a position.

**No timing, and no permanence.** Enforcement is a per-date constraint on the
displayed price and evaporates when the source withdraws the row: a region
demanding `p(φ) ≥ 1` leaves exactly one feasible price at that date, and at the
next date with the row withdrawn `p(φ) = 0` is feasible again. A settlement
cannot be withdrawn — stages are nested and settlements do not reopen
(`NL-SI-P1`) — so the coherence polytope stays cut, and mispricing a settled
sentence stays exploitable. Both halves are computed in the same test class.

The three verbs the settlement interface uses for a settlement event —
*constrains*, *pays*, *grounds* — are therefore untouched by traderization. What
traderization changes is the fourth thing, which the interface calls the weight
standing behind what is written.

## 6. The equivalence question, answered against a stated relation

Using the four relations of `SOURCE_AUDIT.md` §4:

- **R1, identical finite-time prices — false.** `ENFORCEMENT.md` §4 exhibits a
  date where the enforced market has one feasible price and the unmodified market
  has many.
- **R2, both satisfy the criterion relative to the same `D` — true**, by
  Corollary 10, since the coherence-polytope presentation is world-inclusive.
- **R3, the same asymptotic properties — true given R2**, since every §4 property
  of the paper is derived from the criterion alone.
- **R4, `D` eliminated from the algorithm — false.** `Budgeter^D` still consumes
  `PC(D_n)`, and `SOURCE_AUDIT.md` §3 shows that removing it costs
  `lem:budgeter`.3 and with it trading-firm dominance.

The honest summary: **traderized enforcement of the coherence polytope adds a
finite-date coherence guarantee to a logical inductor. It does not replace the
deductive process.** The phrase "the traderized deductive process is equivalent to
the original" is false under R1 and R4 and true under R2 and R3, and is not used
in this round without one of those labels attached.

## 6a. Deduction as the calibration case, not the generalisation

The round is not trying to remove `D` from Logical Induction, and §6 says why it
cannot. What deduction is here is the constraint source for which force is
cleanest, and that makes it the instrument against which other sources are read:

```text
deduction              →  coherence region        →  same force mechanism  →  depth 0, liability 0
normative endorsement  →  possibly narrower region →  same force mechanism  →  depth > 0, liability to be bounded
```

One mechanism, two sources, different safety obligations — and the obligation
falls on the *source*, because the per-date liability ceiling `C_t · d_t(W)`
depends on nothing the mechanism chooses. That is the generalisation the round
actually earns: not that every constraint is enforced alike, but that every
constraint is enforced by the same thing and charged differently for it.

The reading that makes normative sources tractable is `FUNDING_AND_SAFETY.md` §4:
a source may exclude live worlds permanently, provided the depth of exclusion
decays against the growth of ordinary volume. Deduction is the degenerate member
of that family, at depth identically zero.

## 7. What it would close upstream

`THEORY_11_SETTLEMENT_INTERFACE.md` §7 lists `D3` as an open sub-problem: either
a computable tolerance schedule tending to zero with prices provably conforming at
every finite date, or a weakening to eventually-coherent-rateless. Theorem 4 with
`β_j = (ε_n + C_n)/δ_n²` produces a computable schedule `δ_n` of the round's own
choosing, with per-date conformance, for the enforced market.

**This does not close `D3`.** `D3` is a statement about the candidate engine
audited there — the pair consisting of a declared deductive process and a market
over it — and this round changes the market by adding a participant. Whether the
modified pair still inhabits the rest of that interface is not examined.

The measure gap *is* now closed. The incoherence functional is a supremum-norm
quantity and the round's modulus is on row violations; by duality the incoherence
is the largest row violation over signed weight vectors of total mass at most
one, so a rational net of those rows converts one to the other up to the net's
resolution — verified on the interface's own displayed instance, where a net at
denominator three recovers `4/15` exactly (`FORCE_INTERFACE.md` §1). What remains
is the presentation cost of §4 and the inhabitation question. It is a candidate
route to `D3(a)` and is filed as one (`INTEGRATION_MAP.md` §5).
