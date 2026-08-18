# Proof closure

**Verdict.** Logical Induction generalizes past deduction: the assessment-process lift of Budgeter and TradingFirm is kernel-checked against the pinned implementation, a compiled price-region trader gives finite-time force, and preservation follows from finite assessed risk capital — which is exactly zero for deduction, so traderized deduction keeps the original criterion and adds finite-time approximate coherence.

Two links in the arc are not kernel-checked and are named in *Conditional* below: the
first-order erasure that makes the modified market a program, and `DistanceComplete`.

Every load-bearing step of the generalized-Logical-Induction / traderized-force arc,
with what it rests on. Where a step is kernel-checked the declaration is named;
where it is not, what is missing is named instead.

Nothing here is registered in `CLAIMS.md`.

## Classes

| class | meaning |
|---|---|
| `SOURCE-EXACT` | a declaration of the pinned dependency, used as its theorem |
| `LEAN-PROVED` | kernel-checked here, sorry-free, axioms `[propext, Classical.choice, Quot.sound]` |
| `PROVED` | proved on paper from stated premises, argument written out here |
| `DERIVED` | composed from named theorems, all of them above this line |
| `EXHAUSTIVE-FINITE` | verified at every point of a stated finite rational domain |
| `WITNESS` | one displayed instance, exact rationals |
| `BLOCKED` | not a mathematical gap; a named transcription obligation |
| `OPEN` | no proof and no counterexample |
| `FALSE` | refuted, with the counterexample kept |

The pinned dependency is `Formalized-Agent-Foundations` at
`1fffea44eece253cda1722568a3adfe34e822f03`, which `lean/lakefile.toml` pins. Paper
citations are by the paper's own `\label`.

---

## I. The original decomposition

`D ⟶ PC(D) ⟶ criterion ⟶ Budgeter ⟶ TradingFirm ⟶ MarketMaker`.

| step | status | where |
|---|---|---|
| the criterion assesses net worth in `PC(D_n)` | `SOURCE-EXACT` | `Trader.Exploits`, `Criterion.lean:1450` |
| `Budgeter` reads `PC(D_m)` twice: the shutoff test and the scaling infimum | `SOURCE-EXACT` | `priorBudgetBreach`, `budgetScaleFeature`, `Budgeter.lean:918` |
| `TradingFirm` reads it only through `Budgeter` | `SOURCE-EXACT` | `tradingFirmBudgetComponents`, `TradingFirm.lean:432` |
| **`MarketMaker`'s bound is uniform over *every* propositionally consistent world** | `SOURCE-EXACT` | `marketMaker_netWorth_lt_one`, `MarketMaker.lean:1434` |

The last row is stronger than the round previously recorded and is what makes the
generalization free on that side. `marketMaker_not_exploited` takes a
`DeductiveProcess` argument, but its proof discards the consistency hypothesis: the
bound `netWorth < 1` holds at all worlds. So no assessment process needs anything of
the market maker.

Two further facts about the source, both used below.

* The enumeration the `Budgeter` quantifies over is **atom tables**, not sentence
  restrictions: `finiteAtomAssignments (budgetAtoms DP Tr n)` filtered by
  `tableConsistent`. `PC(D_n)` is a cylinder over `atoms(D_n)`, which is how the
  source makes the enumeration finite. That is an implementation of the interface
  below, not part of it.
* `EF.listMin [] = EF.const 1`, so the scaling infimum over *no* plausible world is
  `1`. The source's own docstring says the floor theorem is then vacuous.

---

## II. `PC(D) ⟶ L`: the assessment-process generalization

**The interface.** `AssessmentProcess.Assessment` carries `Live : ℕ → PCWorld → Prop`
and, for each date and each finite sentence support, a finite list of payout tables
that is

* **sound** — every listed table is realised by a world live at that date;
* **complete** — every live world's restriction is listed;

together with **support-local nesting**: on any finite support, a world live at
`n+1` is matched there by a world live at `n`.

| step | status | declaration |
|---|---|---|
| net worth reads a world only through its payouts on the traded support | `LEAN-PROVED` | `netWorth_congr_on_support` |
| `lem:budgeter`.1 — the Budgeter reproduces the raw trade when the raw trader is inside budget at every live world | `LEAN-PROVED` | `BudgeterAt_value_eq_of_safe` |
| `lem:budgeter`.2 — the budgeted trader has the uniform floor `-b` at every live world | `LEAN-PROVED` | `budgetedTrader_netWorth_floor` |
| `lem:budgeter`.3 — an exploiting trader survives some positive budget | `LEAN-PROVED` | `exists_budgetedTrader_exploits` |
| `lem:tfdom` — an exploiting efficiently computable trader makes the firm exploit | `LEAN-PROVED` | `AssessmentFirm.trading_firm_dominance` |
| the recursive market is not exploited by the firm it faces | `LEAN-PROVED` | `AssessmentFirm.firmTrader_not_exploited` |
| **`MarketMaker(TF^L)` satisfies `LIC_L`** | `LEAN-PROVED` | `AssessmentFirm.no_efficient_trader_exploits` |
| the criterion form, with market computability as the one hypothesis | `LEAN-PROVED` | `AssessmentFirm.isLogicalInductor_of_computableMarket` |

These are against the dependency's own `Strategy n`, `Trader`, `EF`, `PCWorld`,
`MarketMaker` and `EfficientlyComputable`. Nothing is a structurally similar finite
model.

### What the round assumed and the proofs do not use

| round's hypothesis | status after formalization |
|---|---|
| (L1) global nesting `L_{t+1} ⊆ L_t` | **not used.** Only its support-local shadow is. `lateAllTrueLive` satisfies the whole interface with `Live 1 ⊆ Live 0` false (`lateAllTrueLive_not_globally_nested`, `WITNESS`) |
| (L2) *effective* finite restriction | **not used by the algebra.** The Budgeter lemmas need the lists finite, not computable. Effectiveness is what makes the market a program, tracked separately in VII |
| (L3) nonemptiness | **not used.** The infimum over an empty list is `1` and every conclusion over live worlds is vacuous. It reappears in §5's properties, not in the construction |

**Correction to `PAPER_RECONCILIATION.md` §2.** Its table gives `lem:budgeter`.1
"(L2) only" and attributes nesting to `.2`. In the formalization nesting is consumed
by `.1` as well: `budgetScaleFeature_denote_eq_one_of_safe` needs the available
capital `b + priorNetWorth` positive, and that is exactly where a world live at `n`
has to have been live at `n-1`.

**Where the two nestings coincide.** For a family whose membership is forced by
having every finite restriction realised inside it, support-local nesting gives
global nesting: `Assessment.live_subset_of_finiteDetermined` (`LEAN-PROVED`).
`PC(D_n)` is such a family (`finiteDetermined_consistentWith`); `lateAllTrueLive` is
not. This is the same property the source's limit-semantics results need, through
compactness, to turn stagewise nonemptiness into a completion.

### The specialization, and that the generalization is proper

| step | status | declaration |
|---|---|---|
| `Live_t = PC(D_t)` is an assessment process | `LEAN-PROVED` | `ofDeductiveProcess` |
| `LIC_L` at that instance **is** `LIC_D`, definitionally | `LEAN-PROVED` | `exploits_ofDeductiveProcess` |
| the generalized Budgeter has the same value as the source's, at every date and world | `LEAN-PROVED` | `BudgeterAt_ofDeductiveProcess_value` |
| the two are not the same *syntax* — they enumerate atom tables and payout tables respectively | — | by inspection of the two definitions |
| **some assessment process is `PC(D_n)` for no deductive process at all** | `LEAN-PROVED` | `allTrueLive_not_deductive` |
| the interface is inhabited | `LEAN-PROVED` | `assessment_is_nonvacuous` |

The last-but-one row is what stops "generalized LI" from being a reparametrization.
Propositional consistency with a finite stage cannot see the atoms the stage does not
mention, so `PC(D_n)` is always a cylinder over a finite atom set; the process whose
only live world is the all-true valuation is not.

---

## III. Why `L` is not enough semantic state

Support does not carry quantitative credal restrictions. `μ(φ) ≥ 1/2` and
`μ(φ) ≥ 3/4` leave the same worlds live and are different constraints, so `L` cannot
distinguish them. `test_semantics.SamePriceProjectionDifferentLiveWorlds` and
`test_semantics.SmallSupportHidesLargeLoss` display both directions of the
independence (`WITNESS`, unchanged from the previous pass).

---

## IV. `C ⟶ (L, K)`, and the projection loss

| step | status | where |
|---|---|---|
| `C ⊆ π⁻¹(π(C))`, with equality exactly for fibre-saturated `C` | `PROVED` | `SEMANTIC_PROJECTION.md` Props 1–3 |
| the inclusion is strict: `Δ({00,11})` and the anticorrelated mixture share a projection | `WITNESS` | `test_semantics.ProjectionLosesSupport` |
| same projection, different live worlds and different support capacities | `WITNESS` | `test_semantics.SamePriceProjectionDifferentLiveWorlds` |
| `C_{t+1} ⊆ C_t ⟹ L_{t+1} ⊆ L_t`, and the converse fails | `PROVED` | `test_semantics.Nesting` |
| `Live(Δ(PC(D_t))) = PC(D_t)`, both directions | `PROVED` | `test_semantics.DeductiveSemanticRecovery` |

`C_{t+1} ⊆ C_t` is **sufficient and not necessary** for the nesting the construction
needs, and the construction needs less again — support-local nesting of `L`. So no
monotonicity has to be imposed on credal constraints.

---

## V. `K ⟶ E`: traderized force

### The trader is a trading strategy

| step | status | declaration |
|---|---|---|
| the compiled position is a `LogicalInduction.Strategy n` | `LEAN-PROVED` | `EnforcementStrategy.enforcementStrategy` |
| every coefficient has rank `≤ n` | `LEAN-PROVED` | `coefficientFeature_rank_le` |
| the traded support is the presentation's coordinate list | `LEAN-PROVED` | `enforcementStrategy_support` |
| coefficients denote continuous functions of the history | `LEAN-PROVED` | `coefficientFeature_continuous` |
| **its exact rational value is the quantity the force algebra bounds** | `LEAN-PROVED` | `marketValueRat_enforcementStrategy`, `value_enforcementStrategy` |
| the term is a `def`, not a `noncomputable def` | build-enforced | `enforcementStrategy` |

The information-time question is settled structurally rather than by argument: the
intensities are `EF.const` leaves of a term whose arguments are the presentation and
the date, with no market history among them, and the rank bound is what says the
coefficients read no price later than day `n`. There is no rational-approximation gap
to quantify: the market maker's displayed prices are exactly rational and world
payouts are exactly `{0,1}`, so `Strategy.marketValueRat` *is* the value.

### The force algebra

| step | status | declaration |
|---|---|---|
| extremal pinning `max_W ⟪ζ, W−P⟫ = Σ_φ [ζ_φ⁺(1−P_φ) + ζ_φ⁻P_φ]` | `EXHAUSTIVE-FINITE` | `test_enforcement.ExtremalPinning`, cube enumeration |
| the enforcement inequality `Σ_j β_j g_j² ≤ ⟪ζ_E, x−P⟫` at any region point | `LEAN-PROVED` | `weighted_square_le_pair` |
| the liability inequality with deficits | `LEAN-PROVED` | `weighted_square_sub_deficit_le_pair` |
| nonnegative value at any admitted world | `LEAN-PROVED` | `pair_nonneg_of_mem` |
| conformance `Σ_j β_j g_j² ≤ ε + M` at the contract | `LEAN-PROVED` | `weighted_square_le_slack_add_volume` |
| the same, at the actual strategy | `LEAN-PROVED` | `weighted_square_le_slack_add_volume_at_strategy` |
| **per-row tolerance: `β_j ≥ (ε+M)/δ²` and `0 < ε+M` give `g_j ≤ δ`** | `LEAN-PROVED` | `rowViolation_le_of_intensity_ge` |

**Narrowed.** `β_j ≥ (ε+M)/δ²` alone does not give `g_j ≤ δ`. At `ε+M = 0` the
condition is met by `β_j = 0`, and then the conformance bound holds at every price
while no row is constrained. The hypothesis `0 < ε+M` is automatic in the source
market, whose slack is `2^{-(n+1)}` at every date.
`test_regressions.PerRowToleranceNeedsPositiveDisturbance`.

### From rows to a coherence measure

Per-row conformance is a fact about the displayed rows. Three results say exactly how
much more it gives.

| step | status | where |
|---|---|---|
| **arbitrary presentations are not intrinsic**: `g_j(p) ≤ δ` on every row with `dist_∞(p,K)/max_j g_j(p) = 1/e`, unbounded | `WITNESS` | `test_coherence.ArbitraryPresentationsAreNotIntrinsic` |
| `dist_∞(p,K) = sup_{‖c‖₁≤1}(inf_{x∈K}⟪c,x⟫ − ⟪c,p⟫)₊`, and `inf_{x∈conv V} = min_{v∈V}` | `PROVED` | below |
| soundness: no support-function row ever reports more than the distance | `LEAN-PROVED` | `CoherenceModulus.gap_le_of_mixture` |
| net modulus: conformance `δ` on an `ℓ¹`-net of mesh `m` bounds every support gap by `δ + m` | `LEAN-PROVED` | `CoherenceModulus.gap_le_of_net_cover` |
| the constant `1` is attained, so `δ + m` cannot be improved to `δ + m/2` | `WITNESS` | `test_coherence.TheLipschitzConstantIsOne` |
| **the exact dual-distance presentation: a finite rational row family with `max_j g_j(p) = dist_∞(p,K)` for every `p`** | `PROVED` + `EXHAUSTIVE-FINITE` | below; `test_coherence.ExactDualDistancePresentation` |
| the exact family is world-inclusive by construction | `LEAN-PROVED` | `IntrinsicCoherence.rhss_le_pair_at_world` |
| the exact family is a function of `K`, not of the generators | `EXHAUSTIVE-FINITE` | `test_coherence.TheExactFamilyIsCanonical` |
| **intrinsic force**: conformance `δ` under a distance-complete support presentation exhibits an admissible credence within `δ` of the prices | `LEAN-PROVED` | `IntrinsicCoherence.exists_credence_of_contract` |

**The duality.** For nonempty closed convex `K` and any `p`: `≥` because
`⟪c,x−p⟫ ≤ ‖c‖₁‖x−p‖_∞ ≤ ‖x−p‖_∞` at the nearest point; `≤` because for `δ'` below
the distance `p ∉ K + δ'B_∞`, which is closed and convex, so a separating functional
exists, and normalising it by its `ℓ¹` mass and negating gives a `c` in the unit ball
with gap above `δ'` — the `B_∞` support term is `δ'‖c‖₁` because `ℓ¹` is the `ℓ^∞`
dual. For `K = conv V`, linearity of `⟪c,·⟫` puts the infimum at a generator. The
repo's `⟪c,x⟫ ≥ r` orientation is the second form; the first form of the same
identity is the substitution `c ↦ −c`, and the unit ball is symmetric.

**The exact family.** `F(p) = max{ν − ⟪c,p⟫ : (c,ν) ∈ D}` where
`D = {(c,ν) : ‖c‖₁ ≤ 1, ν ≤ ⟪c,v⟫ ∀ v ∈ V}`, because for fixed `c` the best `ν` is
`min_v⟪c,v⟫`. `D` depends on `V` alone and `p` enters only the linear objective. `D`
is pointed — a line would need direction `(0, ±t)`, and `+t` eventually violates
`ν ≤ ⟪c,v⟫` — its recession cone is `{(0,−t) : t ≥ 0}`, and the objective tends to
`−∞` along it, so the maximum is attained at an extreme point of `D`. `ν` is
bounded above but not below on `D`, and at an optimum `ν = min_v⟪c,v⟫ ∈ [−1,1]`
because `|⟪c,v⟫| ≤ ‖c‖₁‖v‖_∞ ≤ 1` on the cube; no normalisation is added, since
the extreme-point argument does not need one. Splitting the ball
by which generator attains the minimum,

    R_v = { c : ‖c‖₁ ≤ 1, ⟪c,v⟫ ≤ ⟪c,v'⟫ for every v' ∈ V } ,

the objective is linear on each `R_v`, which is bounded, so its maximum there is at a
vertex. Hence

    N*(V) = ⋃_{v ∈ V} vert(R_v),   rows  ⟪c,x⟫ ≥ min_{v∈V}⟪c,v⟫  for c ∈ N*(V)

is finite, rational, computable from `V`, independent of the price, and its largest
violation is `dist_∞(p, conv V)` at every `p`. Three corollaries: it is an exact
`H`-representation of `K`; every row holds at every generator, so world-inclusivity
and therefore `B = 0` are automatic however many rows it has; and adding a generator
inside the hull of the others adds an implied constraint, so `D` — and the row family
— depend on `K` alone.

`src/coherence.py` computes the family by exact rational vertex enumeration and
computes `dist_∞` **independently**, by enumerating the distance program's basic
solutions. On the settlement interface's three-world instance the family has 11 rows
and matches at all 64 grid points, reporting `4/15` at the interface's own price. On
the four-sentence Boolean fragment it has 17 rows and matches at all 81 grid points,
against 40 and 128 net rows that achieve no exactness and under-report — at one price
the distance is `1/3` and the coarse net reports zero.

**The one unformalized link.** `DistanceComplete` states exactness at the type the
force theorem consumes; the theorem above establishes it, and the enumeration
verifies it, but it is not kernel-checked. It is convex duality for a finite rational
polytope, equivalently the finite minimax theorem, and Mathlib carries neither that
nor a convenient `ℓ^∞`/`ℓ¹` separation over `Fin d → ℝ`.
`CoherenceModulus.gap_le_of_distanceComplete` proves the interface cannot be met
vacuously, since soundness forces any witnessing `δ` to be at least the distance.

---

## VI. Safety and preservation

| step | status | declaration |
|---|---|---|
| the realized aggregate's net worth splits into firm plus added trader | `LEAN-PROVED` | `EnforcementPreservation.realizedAggregate_netWorth` |
| the ordinary aggregate's plausible upside is `1 + B` from assessed liability `−B` | `LEAN-PROVED` | `EnforcementPreservation.realizedFirm_netWorth_le` |
| **bounded assessed liability ⟹ `LIC_L` preserved** | `LEAN-PROVED` | `EnforcementPreservation.no_efficient_trader_exploits` |
| the criterion form | `LEAN-PROVED` | `EnforcementPreservation.isLogicalInductor_of_computableMarket` |
| per-date nonnegativity sums to cumulative nonnegativity | `LEAN-PROVED` | `EnforcementPreservation.netWorth_nonneg_of_day_nonneg` |
| the declared-quantity ceiling `(ε_t + M_t)‖d_t(W)‖₁/δ_t` | `DERIVED` from the liability inequality | `test_contract.LiabilityCeiling` |
| a summable ceiling gives a uniform cumulative bound | `DERIVED` | `NORMATIVE_SAFETY.md` §7–8 |
| the support-capacity bridge, as an alternative route | `PROVED` | `test_semantics.SupportBridge` |
| **necessity of the safety condition** | `OPEN` | `PRIORITIES.md` item 40 |

The added trader is an arbitrary `AdaptiveTrader`: being an enforcement trader is not
used, only bounded assessed liability. `B` is not a hypothesis about intensities or
about the region — it is a hypothesis about the trader's cumulative value at assessed
worlds, and nothing else enters.

**The quantifier, stated exactly.** `hliab` is
`∀ n, ∀ v, L.Live n v → −B ≤ (realizedEnforcer).netWorth (history) v n`: for every
date and every world live *at that date*, the cumulative value through that date is
above `−B`. Not "every world live forever", and not a per-date bound. That is what
`realizedFirm_netWorth_le` consumes and what dominance needs, because the plausible
assessments of a trader are indexed by exactly those pairs.

**Necessity is open, and why.** The forward direction discards information: from
`W(Σ E_t) ≥ −B` we bound `W(Σ TF_t) ≤ 1 + B` and then use dominance. Reversing it
would need, from unbounded enforcement liability, the construction of an
*efficiently computable* trader exploiting the market — and the enforcement trader
itself is not in that class, so it cannot serve as the witness. The round keeps the
persistent one-sided exploitation instance as a witness that liability can be
unbounded and the market can be exploited together
(`test_safety.SupportCoverageFailure`), which is not a converse.

---

## VII. The generalized construction

Let `C_t` be a semantic credal process, `L_t = Live(C_t)`, `K_t = π_t(C_t)`. Assume

1. `L` satisfies the `Assessment` interface — sound and complete finite
   restrictions, support-local nesting;
2. `K_t` has a finite rational presentation at each date, and the presentation is
   available before the market maker chooses `P_t`;
3. the market `MarketMaker(TF^L + E^K)` is a computable belief sequence;
4. `E^K`'s assessed cumulative value on `L` is bounded below by `−B`.

Then `MarketMaker(TF^L + E^K)` satisfies `LIC_L`
(`EnforcementPreservation.isLogicalInductor_of_computableMarket`, `LEAN-PROVED`) and
carries the per-date conformance of V (`LEAN-PROVED`), which is intrinsic when the
presentation is the exact dual-distance family of a rational `K_t`.

**Hypothesis 3 is `BLOCKED`, and it is a transcription.** Three of the four things a
compiler needs are present:

* the emission side is executable — `BudgeterAt`, `TradingFirmAt` and
  `enforcementStrategy` are `def`s, the same status as the dependency's own
  `BudgeterAt` and `TradingFirmAt`, and the build enforces it;
* the search side is generic in the strategy —
  `LogicalInduction.marketMakerSearchUpTo` is an executable bounded search and
  `MarketMaker_search_clock` returns the answer at a finite clock for *every*
  `Strategy n`;
* the recursion is prefix-determined —
  `EnforcementPreservation.aggregateAt_eq_of_eq_prefix` (`LEAN-PROVED`).

What is absent is the erasure: the first-order presentation of the whole recursion
that `Construction/LIACompiler.lean` builds for its own aggregate, in 7300 lines.
Nothing in the modification changes its character; this pass did not do it.

**Computable, not efficient.** `EfficientlyComputable` is required of the traders the
criterion quantifies over. The enforcement trader is not one of them, and presenting
a coherence polytope can cost exponentially in the priced fragment. No complexity
claim is made beyond computability.

Not in this theorem, and not claimed anywhere: legitimacy of `C_t`; derivation of
`C_t` from a normative record (`PRIORITIES.md` item 39); necessity of the safety
condition (item 40); exact enforcement; efficiency; semantic recovery from `K_t`
alone.

---

## VIII. Traderized deduction

Specialize to `C_t^D = Δ(PC(D_t))`, so `L_t^D = PC(D_t)` and
`K_t^D = conv(PC(D_t)|_{Φ_t})`.

| step | status | declaration |
|---|---|---|
| D1 semantic recovery `Live(Δ(PC(D_t))) = PC(D_t)` | `PROVED` | `test_semantics.DeductiveSemanticRecovery` |
| D2 `K_t^D` is the coherence polytope of the fragment | `PROVED` | by definition of `conv`; `test_deduction.SupportPresentation` |
| D3 zero liability: the enforcement value is `≥ 0` at every deductively plausible world, at every date | `LEAN-PROVED` | `DeductiveEnforcement.enforcement_day_value_nonneg`, `enforcement_netWorth_nonneg` |
| **D4 the modified market satisfies the ORIGINAL `LIC_D`** | `LEAN-PROVED` | `DeductiveEnforcement.no_efficient_trader_exploits`, `..._of_worldInclusive` |
| the criterion form, as the dependency's own structure | `LEAN-PROVED` | `DeductiveEnforcement.isLogicalInductor_of_computableMarket` |
| D6 finite-time coherence, intrinsic | `LEAN-PROVED` modulo `DistanceComplete` | `IntrinsicCoherence.exists_credence_of_contract` |
| D7 the presentation's cost | `EXHAUSTIVE-FINITE` counts; no tight bound proved | `test_coherence.TheDeductivePresentationIsComputable` |

D4 runs against the **source's** `TradingFirm` and the **source's**
`trading_firm_dominance`, at its own `DeductiveProcess`. Nothing generalized is used,
so the conclusion is `def:lic` over `D` and not a generalization of it.

**D5, theorem inheritance.** `isLogicalInductor_of_computableMarket` produces the
dependency's `IsLogicalInductor (history DP E) DP`. Every theorem the paper states for
an arbitrary logical inductor over `DP` therefore applies to the modified market,
because it satisfies the definition those theorems are conditioned on. The exceptions
are statements about the particular `LIA` construction rather than about the
criterion — the round found no §4 property of that kind, and the one construction-level
fact that does *not* transfer is finite-price agreement: the modified market differs
from `liaHistory DP` at some date, which is result 1 of the round's ledger and is
`WITNESS`.

**Why `δ_t` is unconstrained here.** In the deductive case the liability is zero for
*any* nonnegative intensities, because every plausible world satisfies every row of a
world-inclusive presentation and `pair_nonneg_of_mem` needs only `β ≥ 0`. So the
intensity may be as large as the tolerance schedule demands, at no cost in liability
and with no affordability side-condition. That is the sense in which deduction is the
strong calibration case.

**The fragment schedule.** `Φ_t` may be *any* finite set of sentences at each date,
and the schedule may be any computable one — including a nested exhausting schedule
`Φ_t ⊆ Φ_{t+1}` with `⋃_t Φ_t = Sentences`. Nothing in the construction constrains
it: `enforcementStrategy pres n` has rank `≤ n` whatever `pres.coordList` is, its
support is finite whatever `Φ_n` is, and the market maker is total on any
`Strategy n`. What is **not** claimed is simultaneous finite-time coherence on the
whole infinite language; the claim is that every sentence eventually enters a fragment
carrying an explicit finite-time guarantee.

**Computability of the deductive presentation.** `V_t = PC(D_t)|_{Φ_t}` is computed
from the finite atom context `atoms(D_t) ∪ atoms(Φ_t)` by the source's own
`finiteAtomAssignments` filtered by `tableConsistent` — this is `deductiveRestrict`.
Its members are `{0,1}`-rational. Vertex enumeration over `ℚ` is computable and its
outputs are rational. The family depends on `D_t` and `Φ_t` only, so it is emitted
before the market maker chooses `P_t`. The only proved size bound is crude: the dual
polyhedron has `2^{|Φ_t|}` sign facets and `|V_t|` support facets in dimension
`|Φ_t| + 1`. Observed counts are far smaller — 11 rows at `|Φ| = 3`, 17 at `|Φ| = 4` —
and no tight bound is claimed. Row count does not affect safety: every row of a
support-function presentation is valid at every plausible world.

---

## Which Logical Induction property families generalize

Reading the source, every paper-facing `lic_*` theorem's dependence on the deductive
process factors into exactly three hypotheses:

1. the criterion, `[IsLogicalInductor P DP]`;
2. **stagewise nonemptiness**, `∀ n, ∃ v, v.ConsistentWith (DP.D n)` — which is the
   round's (L3), appearing here and not in the construction;
3. a condition on what the assessed worlds say, in one of two shapes: *semantic*,
   `∀ n v, v.ConsistentWith (DP.D n) → …`, which transfers by substitution; or
   *syntactic*, `φ ∈ DP.D n`, which the proofs consume **only** by deriving its
   semantic consequence.

| family | status under arbitrary `L` |
|---|---|
| provability induction (`thm:provind`) | **GENERALIZES VERBATIM** — `AssessmentProperties.lic_affirmed_tendsto_one`, `LEAN-PROVED` |
| coherence, refutation half | **GENERALIZES VERBATIM** — `AssessmentProperties.lic_refuted_tendsto_zero`, `LEAN-PROVED` |
| coherence, additivity under exclusion; price convergence | **GENERALIZES VERBATIM** — audited by hypothesis shape |
| affine persistence, preemptive learning, affine provability | **GENERALIZES VERBATIM** — audited by hypothesis shape |
| limit coherence, the *price* conclusion (`lic_limitingBelief_gaifman`) | **GENERALIZES VERBATIM** — hypotheses are the criterion and stagewise nonemptiness only |
| expectation properties, linearity, expectation convergence | **GENERALIZES VERBATIM** — their world conditions are already of the semantic shape |
| calibration, non-dogmatism, uniform non-dogmatism, Occam bounds, self-trust, introspection, timely learning, relationships, hysteresis, pseudorandomness | **GENERALIZES AFTER REPLACING A SYNTACTIC HYPOTHESIS BY ITS SEMANTIC CONTENT** — `φ ∈ D n` becomes "every world assessed at `n` affirms `φ`" |
| limit coherence, the *measure-support* conclusion (`lic_gaifmanMeasure_supported`) | **REQUIRES EXTRA STRUCTURE ON `L`** — its conclusion is about `ConsistentWithTheory DP`, and replacing it needs `⋂_n L_n` to be nonempty and measurable |
| affine coherence (`PolySequence.affcoh`) | **REQUIRES EXTRA STRUCTURE ON `L`** — its conclusion references values at worlds consistent with *every* stage, whose nonemptiness comes from `exists_consistentWithTheory`, i.e. from closedness plus compactness. `⋂_n L_n` can be empty with every `L_n` nonempty |
| conditioning (`lic_conditioned`) | **SPECIFIC TO DEDUCTION** as stated — its conclusion is `IsLogicalInductor … (DP.union extra)`, and "union of processes" has no analogue until an intersection-of-live-sets operation is defined |
| meta-learning (halting patterns, finitistic consistency) | **SPECIFIC TO DEDUCTION** in content — the hypotheses are facts about particular theories, though the mechanism generalizes by the substitution above |
| universal semimeasure | **NOT AUDITED** — its machinery is bit-prefix sentences and a deductive-process construction, and this pass did not read it |

Two things this table separates and the round previously did not: "prices converge"
generalizes, while "the limit is a probability measure over completions of `Γ`" does
not without closedness. And the extra structure that the second needs is exactly
`FiniteDetermined`, the same property that collapses the two nesting notions.

**Evidence for the classification.** Two families are transcribed and
kernel-checked. The rest is a reading of hypothesis shapes, arrived at by extracting
every `lic_*` signature from the source and by reading two proofs in full
(`sellDaily_exploits_freq`, `buyDaily_exploits_freq`) to confirm that the syntactic
hypothesis is consumed only semantically. It is not a re-derivation of each family.

---

## Confidence-kill questions

**K1. Does generalized `lem:budgeter`.3 use proof-theoretic facts about `D`?** No.
`exists_budgetedTrader_exploits` uses only the definition of exploitation and part 1.
Kernel-checked.

**K2. Does `lem:tfdom` use more of `D` than the audit noticed?** No. Its
DP-dependence is entirely through `BudgeterAt`; weights, cutoffs, `ℓ¹` strategy
bounds, the gate and the trader enumeration mention no worlds. `firmRaw_netWorth_abs_lt_cutoff`
is world-universal in the source. Kernel-checked by transcription.

**K3. Is `restrict(t,S)` enough, or does some term need a global world?** Enough, and
in a sharper form than the round stated: the only fact used is
`netWorth_congr_on_support` — net worth reads a world through its payouts on the
traded support. No source term needs a global witness. Kernel-checked.

**K4. Can `MarketMaker` consume `TF^L + E` without a rank or complexity failure?**
Yes. `Strategy.join` of two `Strategy n`s is a `Strategy n`, `MarketMaker` is total on
any `Strategy n`, and the fixed-point lemma's hypotheses are properties of the
strategy type. `EnforcementPreservation.aggregateAt` is that join and the recursion
elaborates. Kernel-checked.

**K5. Does the compiled trader preserve continuity?** Yes.
`coefficientFeature_continuous` is the source's `EF.continuous_denote` at the
compiled term. Kernel-checked.

**K6. Is `M_t` available before `β_t` is chosen, with no circularity?** Yes, and the
argument is structural rather than numerical. `M_t` is bounded by the source's own
computable volume bound, which the `TradingFirm` construction produces from the belief
history — a function of dates `< t`. `β_t` enters the compiled term as `EF.const`, and
the term's arguments are the presentation and the date; no market history is among
them. That the generalized firm or the enforcement trader changes the belief history
is irrelevant, because the bound is computed *from* whatever history obtained, at
information time `t`. `test_regressions.IntensityIsFixedBeforeThePrice`.

**K7. Does the conformance proof use a point of `K` whose witness is unavailable?**
It uses one as a hypothesis, `hx : ∀ i, r_i ≤ ⟪c_i, x⟫`, and the theorem is stated
with `x` universally quantified — so no existence is assumed. For a support-function
presentation any generator serves and the witness is explicit
(`IntrinsicCoherence.rhss_le_pair_at_world`). Theorem existence and algorithmic
availability are therefore not conflated.

**K8. Does bounded enforcement liability give the exact upper bound `tfdom` needs, at
the right dates?** Yes, and the exact quantifier is in VI.
`realizedFirm_netWorth_le` produces `≤ 1 + B` at each `(n, v)` with `v` live at `n`,
which is precisely the index set of `plausibleAssessments`. Kernel-checked.

**K9. Is `B = 0` truly cumulative under the source's time-indexed `PC(D_n)`?** Yes.
`enforcement_netWorth_nonneg` inducts on the date and uses `DP.mono` to move a world
live at `n+1` back to `n`, which is where the assessment-time question lives.
Kernel-checked.

**K10. Does `LIC_D` imply every advertised guarantee?** It implies every §4 property,
because those are conditioned on the criterion. It does not imply anything about the
*particular* `LIA` prices; the modified market differs from `liaHistory DP` at some
date. The round's ledger keeps that as a witness rather than folding it into the
criterion claim.

**K11. Does finite rowwise coherence imply the advertised metric?** Only for a
distance-complete presentation. For an arbitrary presentation it is **false**, with the
near-parallel witness and ratio `1/e`. For the exact dual-distance family it is true
with no error term. For a support-function net it is true with `+ mesh`. All three are
recorded separately in V.

**K12. Is full coherence effectively presentable at every finite date?** Yes, for the
finite fragment: `V_t` is computable from the finite atom context and the row family
by rational vertex enumeration. Computable; not efficient; no tight size bound.

**K13. Does `K_t = π_t(C_t)` carry what the force compiler needs when `C_t` is not
polyhedral?** Not in general. The compiler consumes a finite rational row family, and
the intrinsic theorem consumes a distance-complete one, which the construction of V
supplies for a rational polytope given by generators. For a non-polyhedral `C_t` the
round assumes a finite rational polyhedral interface and says so; that is hypothesis 2
of VII.

**K14. Is `C_{t+1} ⊆ C_t` required?** No. It is sufficient for live-set nesting, and
live-set nesting is itself stronger than the support-local nesting the construction
consumes. No monotonicity on credal constraints is imposed.

**K15. Could the source alter `C_t` with `L_t` fixed and break safety?** Yes, and it
is handled rather than lost. `L_t` fixed leaves `LIC_L` untouched, but `K_t = π_t(C_t)`
can move, changing which rows are enforced and hence the liability. That is why safety
is stated as a hypothesis about the enforcement trader's assessed cumulative value and
not as a hypothesis about `L`. In the deductive case the two cannot come apart, because
`K_t^D` is generated by `L_t^D`.

---

## What this does not establish

* The market is a computable belief sequence. `BLOCKED` on the erasure, VII.
* `DistanceComplete` is not kernel-checked. V.
* The safety condition's necessity. `OPEN`.
* `C_t` from a normative record. `OPEN`, `PRIORITIES.md` item 39.
* The exactness conjecture (face solidity) is untouched by this pass, and nothing in
  I–VIII depends on it.
* The property-family classification is by hypothesis shape for all but two
  families, and the universal-semimeasure family was not read.
* No tight bound on the exact presentation's size.
* Nothing here is registered, and no epistemic class above `test-supported` is
  claimed for any Python result.
