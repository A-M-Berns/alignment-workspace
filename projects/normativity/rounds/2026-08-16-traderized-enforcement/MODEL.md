# The model

Every object the round uses, with its type. Names marked *provisional* are
proposals, listed in the round report and the pull request.

## 1. The priced fragment

At date `n` a bounded reasoner prices a finite set of sentences `Φ_n`. Prices are
a vector `P_n ∈ [0,1]^{Φ_n}` with rational entries. A **world** restricted to the
fragment is a vector `W ∈ {0,1}^{Φ_n}`, so worlds are cube vertices and the same
pairing `⟪u, v⟫ = ∑_φ u_φ v_φ` applies to prices and worlds alike. `PC(D_n)` is
the set of worlds propositionally consistent with the deductive stage.

Deductive stages are nested, so `PC(D_n) ⊆ PC(D_m)` for `m ≤ n`: the plausible
set shrinks.

## 2. Positions

A day-`n` trading strategy is determined by its share coefficients `ξ ∈ ℝ^{Φ_n}`,
which may depend continuously on the displayed prices. Its cash term is fixed:
`-⟪ξ, P_n⟫`. So its value in a world is

    val(ξ, P, W) = ⟪ξ, W - P⟫ ,

zero at `W = P`. Three derived quantities, each used with its own name because
collapsing them is how the construction can be made to look better than it is:

    maxgain(ξ, P) = max over W ∈ {0,1}^Φ of val   = ∑_φ [ ξ_φ⁺ (1 - P_φ) + ξ_φ⁻ P_φ ]
    worstloss(ξ, P) = -min over W ∈ {0,1}^Φ of val
    plausible value = val(ξ, P, W) for W ∈ PC(D_n)

`market.max_gain` and `market.min_value` compute the first two exactly; a test
checks both against brute enumeration over the cube.

## 3. The admissible region

`K_n ⊆ [0,1]^{Φ_n}` is presented as a finite system of rational rows
`⟪c_j, x⟫ ≥ r_j`, `j ∈ J_n`. The presentation, not the set, is what the
mechanism consumes: two row systems cutting out the same set compile to different
traders and enforce differently under slack.

Row violations at a price:  `g_j(P) = max(0, r_j - ⟪c_j, P⟫)`.

What the proofs actually consume:

| assumption | consumed? |
|---|---|
| `K_n ≠ ∅` inside the cube | **yes** — every theorem evaluates at a region point |
| closed | yes, implicitly: rows are non-strict |
| convex | **not directly.** The theorems use only that the rows hold at one region point. Convexity is what makes a *presentation by rows* possible at all |
| relative-interior or core condition | **no** |
| effective presentation at date `n` | **yes** for the algorithm, not for the inequality |
| time variation | **no constraint.** Every enforcement statement is per date and survives arbitrary variation of `K_n`. The safety statements do not |
| compatibility with settlement | **not by enforcement.** It is the separate condition of §4 |

Nonemptiness is where "the region must be reachable" lives. Without a point of
`K_n` in the cube there is nothing to evaluate the enforcement inequality at, and
`enforcement.Region` carries the requirement as a documented precondition rather
than a checked invariant.

## 4. World-inclusive regions *(provisional)*

`K_n` is **world-inclusive** at date `n` when every `W ∈ PC(D_n)` satisfies every
row. This is the round's disambiguated stand-in for what the dispatch calls
support coverage; it is not identified with `coverage(Due)` and the two have
different types (see `INTEGRATION_MAP.md` §3).

One presentation makes it automatic. The **support-function presentation**
*(provisional)* takes a finite family `C` of rational coefficient vectors and
sets

    K_n(C)  =  { x ∈ cube : ⟪c, x⟫ ≥ min over W ∈ PC(D_n) of ⟪c, W⟫,  for c ∈ C } .

Reading the right-hand side off the plausible worlds makes world-inclusivity hold
by construction, makes `K_n(C)` contain the coherence polytope
`conv(PC(D_n))`, and makes it equal that polytope once `C` carries the polytope's
facet normals. `deduction.support_rows` builds it; a test confirms both the
inclusion property and, on a Boolean fragment, the equality.

The dichotomy is sharp and is the round's organising fact. A row with
`r_j ≤ min_{W plausible} ⟪c_j, W⟫` excludes no plausible world. A row with
`r_j >` that minimum excludes one, and that is exactly the case where enforcement
can cost something.

## 5. The enforcement trader *(provisional)*

The **constraint-to-trade compiler** maps a row presentation and a vector of
positive **enforcement intensities** `β_j` to one day-`n` strategy, the
**violation-proportional position**:

    ζ_E(P)  =  ∑_{j ∈ J_n}  β_j · g_j(P) · c_j .

What this is as a trade, not as a functional. On the sentence `φ` it holds
`ζ_E(P)_φ` shares — long where positive, short where negative. It pays
`⟪ζ_E(P), P⟫` for them at the displayed price, which is the cash term, so the
position is worth zero the moment it is taken. It pays out `⟪ζ_E(P), W⟫` when
the world is `W`. It gains when the price violates the constraint: at any `P`
outside `K_n`, `maxgain(ζ_E(P), P) > 0`, checked pointwise over a grid in
`test_enforcement.SeparatingPortfolio`. Its downside is `worstloss(ζ_E(P), P)`,
which is where funding appears and is accounted in `FUNDING_AND_SAFETY.md`.

**Legality.** `ζ_E` is built from price features, rational constants, addition,
multiplication and `max`, so it is an expressible feature in the sense of
`def:tf` and the compiled object is a trading strategy rather than a function
written down outside the framework. It is continuous, so `lem:fpl`'s Brouwer
hypothesis survives its addition to the aggregate. **[reading]** the modified
algorithm therefore still produces a computable belief sequence whenever the row
system is computable from the belief history; this is argued from the
construction and is not proved here.

**Not efficiently computable, and not required to be.** The criterion quantifies
over efficiently computable traders; the enforcement trader is in the
price-setting aggregate instead, where only computability is needed. For a
coherence-polytope presentation the row count is exponential in the fragment
(`DEDUCTION_SPECIAL_CASE.md` §4), so this exemption is doing real work.

## 6. Intensity is not funding

`β_j` is a position size. It is not a budget, a credit line, or an amount of
money held. Under an exact contract it does not affect the enforced set at all
(`ENFORCEMENT.md` §2); under slack it sets precision (§3); and in the worked
adversarial fixture the realised position size is set entirely by the opposing
ordinary volume and is *identical* across `β ∈ {10, 100, 1000}`
(`test_safety.IntensityIsNotFunding`).

External funding is tracked separately, in `funding.FundingLedger`, as cumulative
worst-case exposure `F_T = ∑_{n ≤ T} worstloss(ζ_{E,n}, P_n)`: finite at every
finite date by construction, with no uniform bound imposed over dates.

## 7. Objects the exactness and safety questions needed

**Exclusion depth** `d_j(W) = max(0, r_j - ⟪c_j, W⟫)` — how far a row's
right-hand side excludes a point. Zero on every row exactly when the region
contains it, and the second factor in the liability identity.

**Interior-anchored position** — the compiler that achieves exactness where the
violation-proportional one cannot, at the cost of not vanishing on the region.
`exactness.GaugeTrader`, and it refuses an anchor that is not strictly interior,
which is the same test as whether the region has an interior at all.

**Force declaration** — `(rows, C_t, ε_t, intensities, δ_t)`, the five things a
force mechanism signs. `contract.ForceDeclaration` derives the intensity from the
other four and checks conformance squarewise so no root is needed.

**Priceability** — whether a constraint stated over worlds is a functional of
what the market prices. `core.priceable_coefficients`, which returns nothing
rather than approximating.

## 7a. The semantic layer, and four types that must not collapse

The constraint lives in **price** space. What it admits is a set of **credences**.
What the criterion assesses is **worlds**. The pricing map is what joins them, and
reading a credence as a price vector is the error that cost this round its
laundering conclusion.

    world  ω ∈ Ω_t          a `{0,1}` vector over the priced fragment
    credence  μ ∈ Δ(Ω_t)    a distribution over worlds
    price  P ∈ [0,1]^Φ      what the market displays
    pricing map  π_t(μ) = Σ_ω μ(ω)·ω

    compatible credences   C_t = π_t⁻¹(K_t)
    support-live worlds    Ω_t^live = { ω : ∃ μ ∈ C_t, μ(ω) > 0 }
    support capacity       θ_t(ω) = max { μ(ω) : μ ∈ C_t }

`semantics.py` carries all of them, and `dirac_live` is kept — computable and
marked as *not* the definition — so the withdrawn reading stays on the record and
under test.

Liveness and the quantitative coverage hypothesis are the same number at two
thresholds: `ω` is live exactly when `θ_t(ω) > 0`, and coverage asks for
`θ_t(ω) ≥ θ` uniformly. `θ_t` is computed exactly by vertex enumeration of `C_t`,
which is combinatorial in the world count and is why the fixtures stay small.

**The distinction the types enforce.** The enforcement inequality bounds the
position's value at price vectors in `K_t`, and `E_μ[E_t]` is precisely its value
at `π_t(μ)`. So it delivers a bound on **expectations** under admitted credences,
and nothing at any individual world. Bridging to a worldwise bound needs a
hypothesis, and `FUNDING_AND_SAFETY.md` §4a gives two.

## 8. What this model is not

It has no market maker in it. The market maker enters only as the **contract**
`maxgain(ζ, P) ≤ ε_n` on the realised aggregate `ζ = ζ_E + τ`, taken as a
hypothesis and justified in `SOURCE_AUDIT.md` §2. Everything the round proves is
proved from that inequality, so a reader who rejects the reading of the source
loses the application and keeps the algebra.

It has no ordinary traders in it either, only their realised aggregate position
`τ` and a bound `‖τ‖₁ ≤ M_n`. The fixtures instantiate `τ` adversarially rather
than deriving it.
