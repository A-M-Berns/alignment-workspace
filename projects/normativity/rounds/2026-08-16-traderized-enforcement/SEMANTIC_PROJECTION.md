# Semantic constraints and their price projections

The market sees prices. The criterion assesses worlds. Between them sits a
credal set, and the map from the second to the first loses information. That loss
is the round's reason for two channels, and it is a reason about information
rather than about mechanism convenience.

## 1. The objects

    Ω_t                     a finite world space; each ω carries a {0,1} vector over Φ_t
    Δ(Ω_t)                  credences over worlds
    π_t(μ) = Σ_ω μ(ω)·ω     the pricing map, reading off priced marginals
    C_t ⊆ Δ(Ω_t)            the semantic constraint: which credal states are admissible
    Ω_t^live = { ω : ∃ μ ∈ C_t, μ(ω) > 0 }
    K_t = π_t(C_t)          the price-visible projection

`C_t` is primitive. `Ω_t^live` is read off it by support. `K_t` is what a trader
can see and therefore all a trader can enforce. Four types, and the round's worst
errors both came from collapsing two of them.

## 2. Fibre saturation

**Definition.** `Sat_π(C) = π⁻¹(π(C))`: the credences no price observation can
distinguish from `C`.

**Proposition 1.** `C ⊆ Sat_π(C)`. Immediate: `π(μ) ∈ π(C)` for `μ ∈ C`.

**Proposition 2.** Reconstructing semantic admissibility from price-space
membership gives `Sat_π(C)`, not `C`. Immediate from the definition, and it is
the whole content of the projection's information loss.

**Proposition 3.** `C = Sat_π(C)` exactly when `C` is a union of fibres of `π`.
Also immediate, and it is the condition to check rather than to assume.

**Proposition 4 (the witness).** Two priced sentences, four worlds, deduction
admitting only the correlated pair `{00, 11}`. Then

    C^D = Δ({00, 11}),    K^D = π(C^D) = conv{(0,0),(1,1)} = { p_A = p_B } ,

and the anticorrelated mixture `μ = ½δ_01 + ½δ_10` has `π(μ) = (½,½) ∈ K^D`.
So `μ ∈ Sat_π(C^D) ∖ C^D`, and its **entire support is deductively impossible**.
Strict, exact, and minimal in the number of sentences.

**Proposition 5.** The hypothesis "`π` separates the worlds" does not rescue it.
In the same witness `π` is injective on the four worlds — their images are four
distinct price vectors — and the saturation is still strict. Separating points is
not separating mixtures; what would be needed is affine independence of the world
vectors, which four points in a two-dimensional price space cannot have.

`test_semantics.ProjectionLosesSupport` and `.FibreSaturation` carry all five.

## 3. Two credal sets a market cannot tell apart

`C^D = Δ({00,11})` and its saturation have the **same price projection** and
different live worlds: `{00, 11}` against all four, with support capacities
`(1, 0, 0, 1)` against `(1, ½, ½, 1)`. A market watching prices forever cannot
separate them (`test_semantics.SamePriceProjectionDifferentLiveWorlds`).

So the statement the paper can earn is:

> **Finite prices are sufficient coordinates for market force and not, in
> general, sufficient coordinates for the semantic support structure against
> which exploitation is assessed.**

Earned, by Propositions 4 and 5.

## 4. What this does to the architecture

```text
constitutional source
        ↓
      C_t ⊆ Δ(Ω_t)
       ├────────────────→  Ω_t^live  →  generalized exploitation criterion
       │
       └── π_t ─────────→  K_t  →  rows  →  compiler  →  E_t  →  P_t ≈ K_t
```

The left branch is semantics and the right branch is force. They are not two
presentations of one thing: the right branch factors through a map that is not
injective, so no amount of price-space work recovers the left.

**A source that supplies only `K_t` has not supplied a semantics.** It has
supplied a demand, and force can make that demand operative. Reading a semantics
off it requires a **lift**, and the saturated lift `π⁻¹(K_t)` is one choice — the
largest one consistent with what the source said. `semantics.saturated_lift` names
it as a choice rather than deriving it, because a different lift gives different
live worlds and therefore a different criterion.

## 5. Consequences for the round's other results

**Deductive recovery is repaired and improved.** With `C_t^D = Δ(PC(D_t))` the
identity `Ω_t^live = PC(D_t)` holds in both directions by the definition of
support, with no hypothesis about the pricing map at all — forward because a
plausible world's point mass is admissible, reverse because every admissible
credence is supported inside `PC(D_t)`. `DEDUCTION_SPECIAL_CASE.md` §7.

The previous pass proved this from the price region `π(Δ(PC(D)))` and needed a
separation hypothesis it did not have; the witness of §2 shows that route is not
merely unproved but false.

**Support capacity is a property of `C_t`.** `θ_t(ω) = max{ μ(ω) : μ ∈ C_t }`,
computed from the semantic set. Computing it from `π⁻¹(K_t)` gives a different and
generally larger number — `0` against `½` on the witness — and using the second
where the first is meant is the error Proposition 2 predicts.

**Force is untouched.** Every force result is a statement about a price-space
region, a market-maker contract and a position. None mentions `C_t`, `Ω^live`, or
a criterion. That is why the force layer survived four passes of semantic
revision without a single retraction, and it is the reason it is now installed as
a living interface while the semantics is not.
