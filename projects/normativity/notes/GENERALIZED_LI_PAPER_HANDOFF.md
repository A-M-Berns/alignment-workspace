# Generalized Logical Induction — paper handoff

Specification for the next phase: a paper and a small companion Lean artifact. Not a
draft. The research record is
`projects/normativity/rounds/2026-08-16-traderized-enforcement/`, whose
`PROOF_CLOSURE.md` is the arrow-by-arrow status and `THEOREM_MAP.md` the ledger.

The governing standard for the companion artifact:

> Every theorem stated unqualified in the paper has exactly that theorem, with
> essentially the same hypotheses and conclusion, machine-checked in the companion
> artifact.

One obligation stands between today's tree and that standard, and it is named in §C.

Every declaration named below is registered in `projects/normativity/CLAIMS.md` as
`lean-proved`, against the `PRIORITIES.md` item each answers. The registry is what
a claim is; this note states the theorems in the form the paper would.

---

## A. The question and the arc

**Can Logical Induction be generalized past deduction?**

The construction of `arXiv:1609.03543` is stated over a deductive process `D`, but the
object it actually consumes is the evolving family of plausible worlds `PC(D_t)`. That
family enters at two places — the exploitation criterion, and `Budgeter`, hence
`TradingFirm`. The market maker's relevant bound is more general than either: it holds
at every propositionally consistent world, plausible or not.

So the arc is:

```
D_t ⟶ PC(D_t)  ⤳  L_t  ⟶  LIC_L                     (1) assessment processes
                    │
                    │  L_t is only support information: it cannot say μ(φ) ≥ 1/2
                    ▼
             C_t ⟶ (L_t, K_t),  K_t = π_t(C_t)       (2) credal semantics, two lossy maps
                              │
                              ▼
                       rational presentation ⟶ E     (3) traderized force
                              │
                              ▼
                    dist_∞(P_t, K_t) ≤ δ_t           (4) intrinsic conformance
                              │
                              ▼
        bounded assessed downside ⟹ LIC_L preserved  (5) finite risk capital
                              │
                              ▼
   K_t^D = conv(PC(D_t)|_{Φ_t}) ⟹ zero risk capital  (6) deduction revisited
                              │
                              ▼
        LIC_D + finite-time approximate coherence
```

`L_t` drives assessment and non-exploitability; `K_t` is the finite-dimensional price
region to be made operative. Both are lossy images of `C_t`, and neither recovers the
other: two credal sets can share a projection and differ in live worlds, and two can
share live worlds and differ in the quantitative constraints they impose.

Step (5) is the conceptual pivot. A privileged trader with external funding is exactly
what a no-exploitation guarantee is not built to survive; what rescues it is that the
guarantee only ever needed the *ordinary* aggregate's upside bounded, and the market
maker bounds the sum. So the added trader's cumulative downside over assessed worlds is
**risk capital**, and finiteness of it is the whole preservation condition.

Step (6) is why deduction is the strong case rather than merely an instance: every
deductively plausible world lies in the coherence polytope, so the coherence trader's
value there is nonnegative at every date and the risk capital is **exactly zero**. The
original criterion survives untouched, and finite-time approximate probabilistic
coherence is added for free.

---

## B. Proposed theorem spine

Statement sketches at the granularity the companion artifact should expose. Each
carries exactly one class.

### Theorem 1 — Assessment-process Logical Induction

> Let `L` be an assessment process: a family `L_t` of propositionally consistent worlds
> together with, for each date `t` and each finite set `S` of sentences, a finite list of
> payout tables that is sound (each is realised by some world in `L_t`) and complete
> (each world in `L_t` realises one), such that on every finite `S` a world in `L_{t+1}`
> is matched on `S` by a world in `L_t`.
>
> Then `Budgeter` and `TradingFirm` of `arXiv:1609.03543` §5, with `PC(D_t)` replaced by
> `L_t`, satisfy the analogues of `lem:budgeter` 1–3 and `lem:tfdom`, and the recursive
> market `MarketMaker(TF^L)` is not exploited by any efficiently computable trader
> relative to `L`.

`READY FOR PAPER: exactly kernel-supported`. The criterion form's
market-computability premise is discharged for the schedules the paper actually
presents — see Theorem 5 and §C.

Companion declarations: `AssessmentProcess.Assessment`,
`BudgeterAt_value_eq_of_safe`, `budgetedTrader_netWorth_floor`,
`exists_budgetedTrader_exploits`, `AssessmentFirm.trading_firm_dominance`,
`AssessmentFirm.no_efficient_trader_exploits`,
`AssessmentFirm.isLogicalInductor_of_computableMarket`.

**Three remarks the paper should make, because each is a strengthening over the obvious
statement.** Nonemptiness of `L_t` is not a hypothesis — the scaling infimum over an
empty plausible set is `1`, and what nonemptiness buys is non-vacuity of the §4
properties. Global nesting `L_{t+1} ⊆ L_t` is not a hypothesis either, only its
support-local shadow, and the two coincide exactly for families determined by their
finite restrictions. Effectiveness of the restriction lists is not used by the algebra.

**Companion corollaries.** Deduction is an exact specialization —
`exploits_ofDeductiveProcess` makes `LIC_L` at `L = PC(D)` *be* `LIC_D`, and
`BudgeterAt_ofDeductiveProcess_value` makes the two Budgeters the same function of the
history although they enumerate different finite lists. And the generalization is
**proper**: `allTrueLive_not_deductive` exhibits an assessment process whose live set is
`PC(D_n)` for no deductive process, because propositional consistency with a finite stage
cannot see the atoms the stage does not mention.

### Theorem 2 — Finite-time traderized force

> Let `K` be presented by finitely many exact rational rows `⟪c_j, x⟫ ≥ r_j` with
> intensities `β_j ≥ 0`, and let `ζ_E(P) = Σ_j β_j g_j(P) c_j` with
> `g_j(P) = max(0, r_j − ⟪c_j,P⟫)`. Then `ζ_E` is a `LogicalInduction.Strategy n` with
> legal rank, finite support and continuous coefficients, and for any `x` meeting every
> row, `⟪ζ_E(P), x − P⟫ ≥ Σ_j β_j g_j(P)²`.
>
> If the market maker's contract holds for the aggregate at slack `ε` and the ordinary
> aggregate's value against `x − P` is at least `−M`, then `Σ_j β_j g_j(P)² ≤ ε + M`;
> and if `0 < ε + M` and `β_j ≥ (ε + M)/δ²`, then `g_j(P) ≤ δ`.

`READY FOR PAPER: exactly kernel-supported`.

Companion declarations: `EnforcementStrategy.enforcementStrategy`,
`coefficientFeature_rank_le`, `enforcementStrategy_support`,
`coefficientFeature_continuous`, `marketValueRat_enforcementStrategy`,
`TraderizedEnforcement.weighted_square_le_pair`, `weighted_square_le_slack_add_volume`,
`EnforcementStrategy.rowViolation_le_of_intensity_ge`.

**`0 < ε + M` is load-bearing and the paper must carry it.** At `ε + M = 0` the
intensity condition is met by `β_j = 0`, which enforces nothing. It is automatic in the
source market, whose slack is `2^{-(n+1)}`.

**The value identity is the point.** Without
`marketValueRat_enforcementStrategy` the inequalities are algebra about a vector; with
it they are theorems about the strategy the market actually prices.

### Theorem 3 — Intrinsic `ℓ^∞`-distance conformance

> For nonempty closed convex `K ⊆ [0,1]^d`,
> `dist_∞(p,K) = sup_{‖c‖₁ ≤ 1}(inf_{x∈K}⟪c,x⟫ − ⟪c,p⟫)₊`, and for `K = conv(V)` with
> `V` finite the infimum is `min_{v∈V}`.
>
> **(a) Net form.** If the rows are the support-function rows of an `ℓ¹`-net of mesh `η`
> and every row conforms at `δ`, then every support gap is at most `δ + η`; the constant
> `1` is attained, so `δ + η` is sharp.
>
> **(b) Exact form.** For finite rational `V ⊆ [0,1]^d` there is a finite rational row
> family `R*(conv V)`, computable from `V` and independent of the price, with
> `max_{r ∈ R*} violation_r(p) = dist_∞(p, conv V)` for every `p`. It is an exact
> `H`-representation of `conv V`; every row holds at every `v ∈ V`; and it depends on
> `conv V`, not on `V`.
>
> **(c) Force consequence.** Under (b), `β_j ≥ (ε+M)/δ²` and `0 < ε+M` give
> `dist_∞(P_t, K_t) ≤ δ_t` — equivalently, some `μ_t` admitted by `K_t` has
> `max_{φ ∈ Φ_t}|P_t(φ) − E_{μ_t}[1_φ]| ≤ δ_t`.

`READY AFTER NAMED FORMALIZATION DEBT` — see §C, debt 1. (a) and the soundness half are
kernel-supported (`CoherenceModulus.gap_le_of_net_cover`, `gap_le_of_mixture`); (c)
composes through the `DistanceComplete` interface
(`IntrinsicCoherence.exists_credence_of_contract`); the exactness half of (b) is proved
on paper and verified exhaustively over rational grids, not in the kernel.

**The paper must state the negative result beside it.** For an *arbitrary* row
presentation, `g_j(p) ≤ δ` gives no distance bound: two near-parallel rows cutting the
same region have violation-to-distance ratio `1/e`, unbounded. Both presentations are
world-inclusive, so the difference is not safety. Saying "within `δ` of `K`" from rowwise
conformance alone is false, not merely unproved.

### Theorem 4 — Preservation under finite assessed risk capital

> Let `P` be the recursive market pricing `TF^L + E` for an arbitrary added trader `E`,
> and suppose `−B ≤ W(Σ_{t≤n} E_t)` for every `n` and every `W ∈ L_n`. Then
> `W(Σ_{t≤n} TF^L_t) ≤ 1 + B` for the same pairs, and no efficiently computable trader
> exploits `P` relative to `L`.

`READY FOR PAPER: exactly kernel-supported`.

Companion declarations: `EnforcementPreservation.realizedAggregate_netWorth`,
`realizedFirm_netWorth_le`, `no_efficient_trader_exploits`,
`isLogicalInductor_of_computableMarket`, `netWorth_nonneg_of_day_nonneg`.

**Quantifier discipline.** The hypothesis ranges over pairs `(n, W ∈ L_n)`, not over
worlds that stay live forever and not per-date. That is exactly the index set of the
trader's plausible assessments, which is why it is the right hypothesis and not merely a
sufficient one.

**`E` is arbitrary.** Being an enforcement trader is not used. The paper should present
this as a general theorem about adding a privileged participant, with force as the
application.

**Sufficiency only.** The converse — unbounded risk capital implies efficient
exploitation — is open, and the paper must say so rather than implying an equivalence.
The forward direction discards information, and the enforcement trader is not in the
efficiently computable class, so it cannot itself witness a converse. The prospective
risk-account certificate `q_t = (ε_t + M_t)D_t/δ_t` with `Σ_t q_t ≤ B` is a
*conservative sufficient route* to the hypothesis, not an equivalent of it.

### Theorem 5 — Traderized deduction: a finite-time coherent logical inductor

> Let `D` be a deductive process, `Φ_t` any computable finite fragment schedule,
> `δ_t` any computable positive tolerance schedule, and
> `K_t^D = conv(PC(D_t)|_{Φ_t})`. Let `P` be the recursive market pricing
> `TradingFirm(D) + E` where `E` compiles a world-inclusive presentation of `K_t^D`.
> Then the enforcement trader's assessed cumulative value is nonnegative at every date,
> so its risk capital is `0`; `P` satisfies the **original** Logical Induction Criterion
> over `D`; and at every date some `μ_t ∈ Δ(PC(D_t))` has
> `max_{φ ∈ Φ_t}|P_t(φ) − E_{μ_t}[1_φ]| ≤ δ_t`.

`READY FOR PAPER: exactly kernel-supported`, stated as
`DeductiveEffective.deductive_end_to_end`: for any primitive recursive fragment and
tolerance schedules, and any deductive process whose stages are propositionally
satisfiable, the compiled market satisfies the pinned source's own
`IsLogicalInductor` over `D` **and** meets the day-`n` tolerance at every date. It
takes no `ComputableMarket`, no supplied region and no supplied representation, and
it assumes nothing about the deductive process beyond the source's own certificate;
the effective-stage hypothesis that looked necessary is not, because the compiler
carries the stage table as finite data and the source's own Trading Firm reads it
that way. The `ℓ^∞` conclusion follows from the Euclidean one at the same tolerance,
so this statement does not route through debt 1.

Companion declarations: `DeductiveEffective.deductive_end_to_end`;
`EnforcedCompiler.ProjectionSchedule.end_to_end_effective` and
`EffectiveRepresentation.end_to_end_of_constraints_effective` for the two schedule
levels above it; `DeductiveEnforcement.enforcement_day_value_nonneg`,
`enforcement_netWorth_nonneg`, `no_efficient_trader_exploits_of_worldInclusive`,
`isLogicalInductor_of_computableMarket`, `witness_market_not_exploited` for the zero
risk capital and the criterion half.

**Three points the paper should not soften.** The dominance step is the *source's* own
`trading_firm_dominance` at its own `DeductiveProcess`, so the conclusion is `def:lic`
over `D` and not a generalization of it — which is what licenses inheriting every §4
property. `δ_t` is unconstrained: liability is zero for *any* nonnegative intensity, so
there is no affordability side-condition, which is a genuine asymmetry with the general
case. And the cost is real: `|V_t|` is up to `2^{|Φ_t|}` and the row family is
**computable, not efficient** — the result is not efficient finite-time logical
omniscience.

**Inheritance.** Because `P` satisfies the dependency's own `IsLogicalInductor`, every
theorem stated for an arbitrary logical inductor over `D` applies. The one thing that
does not transfer is any statement about the *particular* `LIA` prices: the modified
market differs from `liaHistory D` at some date.

### Proposition 6 — Normative statics as a nonzero-cost application

> `APPLICATION / NOT PART OF CORE THEOREM SPINE`

The motivating normative statics are an instance of the force/risk-capital layer for
priceable constraints. Settlement and coherence rows are liability-free; substantive
endorsement and core rows can consume positive risk capital, and the round exhibits
trajectories that are affordable forever and trajectories that are not.

**What must not be claimed.** That the normative record has been shown to canonically
generate the intended `C_t` or `L_t`. That bridge is upstream, separate, and open
(`PRIORITIES.md` item 39). Traderized enforcement supplies **force**, not legitimacy,
authorization, or corrigibility.

---

## C. Companion Lean artifact plan

The paper should point at a small purpose-built artifact, not at this exploratory round.
Proposed structure, mirroring the spine one file per theorem:

```text
GeneralizedLI/
  Assessment.lean            -- the interface; PC(D) as an instance; properness
  GeneralizedCriterion.lean  -- Budgeter 1-3, tfdom, LIC_L, the recursive market
  Enforcement.lean           -- the Strategy n term and the force inequalities
  IntrinsicDistance.lean     -- the duality, the net modulus, the exact family
  Preservation.lean          -- risk capital and LIC_L preservation
  DeductiveCoherence.lean    -- zero risk capital, original LIC_D, finite-time coherence
  Main.lean                  -- the paper-facing statements, one per theorem, re-exported
```

`Main.lean` is the API: exactly the theorems the paper states unqualified, in the
paper's own phrasing, with no auxiliary hypotheses hidden in a namespace. Everything
today lives in `lean/Workspace/Normativity/Contrib/`, which is the research surface;
extraction is mostly mechanical, and the one thing that is not is below.

### Debt 1 — `DistanceComplete`, `PRIORITIES.md` item 49

The exactness half of Theorem 3(b): from conformance on the exact family, produce an
admissible mixture within `δ`. This is convex duality for a finite rational polytope —
equivalently the finite minimax theorem. Mathlib carries neither a von Neumann minimax
theorem nor a convenient `ℓ^∞`/`ℓ¹` separation over `Fin d → ℝ`, so the work is either

* proving the duality directly over `Fin d → ℝ` via
  `geometric_hahn_banach_point_closed`, which needs `f x = Σ_i c_i x_i` from the finite
  basis, `sup_{‖y‖_∞ ≤ 1}⟪c,y⟫ = ‖c‖₁`, and closedness of `K + δ'B_∞`; or
* proving a finite minimax theorem and specializing.

Interface already in place: `CoherenceModulus.DistanceComplete`,
`gap_le_of_distanceComplete` (the interface cannot be met vacuously),
`IntrinsicCoherence.exists_credence_of_contract` (the composition, waiting on it).
Currently `derived` plus `exhaustive-finite` — `tests/test_coherence.py` verifies it at
every point of stated rational grids against an independently computed distance.
**Estimated small-to-medium and self-contained.** Worth doing in the artifact PR.

### Computability of the modified market — discharged

`EnforcedCompiler.computableMarket` constructs what
`isLogicalInductor_of_computableMarket` used to take as a hypothesis. The four pieces
a compiler needs are all present: the emission side is executable, since `BudgeterAt`,
`TradingFirmAt` and `enforcementStrategy` are `def`s rather than `noncomputable def`s
and the build enforces it; the search side is generic in the strategy, through
`LogicalInduction.marketMakerSearchUpTo` with `MarketMaker_search_clock`; the
recursion is prefix-determined, by
`EnforcementPreservation.aggregateAt_eq_of_eq_prefix`; and the erasure — the
first-order `ℕ`/`List` presentation of the recursion — is supplied by an additive
public section upstream in `Construction/LIACompiler.lean` plus a downstream compiler
that states and proves its own recurrence rather than importing one.

So Theorem 5 is stated unqualified, which is a stronger claim than the source makes
for itself. What it costs is efficiency: the projector generator is **doubly
exponential in the fragment dimension**, stated rather than omitted. A singly
exponential construction plainly exists — the realised upper sets are cells of a
hyperplane arrangement — and needs arrangement-vertex enumeration nobody has
formalized here.

### Everything else

Debt 1 is the only obligation standing between the current declarations and the spine
above, and it is filed as `PRIORITIES.md` item 49. The remaining `open` items —
safety necessity, the normative-record bridge, presentation-cost canonicality, a
tight size bound, the universal-semimeasure property family — are discussion-section
material, not debts against a stated theorem.

---

## D. Suggested paper outline

1. Can Logical Induction be generalized past deduction?
2. `PC(D_t) ⟶ L_t`: assessment processes and `LIC_L`.
3. Why `L_t` is not enough: `C_t ⟶ (L_t, K_t)` and the projection loss.
4. Traderized force.
5. Intrinsic finite-time conformance.
6. Finite assessed risk capital and preservation.
7. Deduction revisited: zero risk cost and finite-time coherence.
8. Normative constraints as a motivating nonzero-cost application.
9. Discussion and limitations.

§9 should carry, plainly: sufficiency without necessity in §6; the conservatism of the
risk-account certificate; `computable` but not efficient in §7; and that force is not
legitimacy. Legitimacy, deference and the broader normative-learning theory stay out of
the core narrative.

---

## Provenance

Generator `prompts/2026-08-16-traderized-enforcement/` (closure pass; executor Claude
Opus 5, Anthropic; dispatch author unrecorded), reconciled against the registered
declarations by `prompts/2026-08-24-reservation-bar-and-debt/` (executor Claude Opus 5,
Anthropic; prompt author Claude Fable 5, Anthropic). Review status `ci-only`. Names
marked provisional under `AGENTS.md` §6, for the naming audit.
