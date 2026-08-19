# Paper closure report

What the strongest defensible version of *Generalizing and Strengthening Logical
Induction* now is, what construction realizes it, and what is left.

The author's decisions of 2026-08-18 are taken as settled here: projection is the paper's
main traderization construction, rows are the secondary special case, `DistanceComplete` is
off the critical path, and the canonical construction uses the **calibrated** intensity.

## 1. The recommended theorem chain

Each line names the Lean declaration that is the statement of record. All are
kernel-checked with no `sorry` and axioms `[propext, Classical.choice, Quot.sound]` only,
except where a hypothesis is named as external.

| # | claim | statement of record |
| --- | --- | --- |
| 1 | Logical Induction's construction consumes an assessment (support) process, not deduction | `AssessmentFirm.*`, `AssessmentProperties.*` (merged) |
| 2 | the generalization is proper | `AssessmentProperties.allTrueLive_not_deductive` (merged) |
| 3 | the market maker's day contract holds on the whole price cube, not only at worlds | `ProjectionMarket.value_le_of_forall_bitWorld`, `marketMaker_day_value_le_cube` |
| 4 | the cube extension is legitimate and discharges the cube hypothesis | `ProjectionCalibrated.isNearestPoint_extend`, `realizes_extend`, `extend_mem_cube` |
| 5 | force: `λ‖q−P‖² ≤ ⟨ζ, y−P⟩` for `y ∈ K` | `ProjectionForce.force_inequality` |
| 6 | zero value at every admitted point | `ProjectionForce.value_nonneg_of_mem` |
| 7 | liability `≥ −λ δ d₂(w,K)` once the price conforms | `ProjectionForce.liability_calibrated` |
| 8 | `λ_n·δ_n = ρ_n/δ_n` **at the calibrated intensity, and only there** | `ProjectionCalibrated.calibratedIntensity_mul` |
| 9 | the calibrated intensity buys the tolerance, with the cube hypothesis discharged | `ProjectionCalibrated.dist2_le_of_calibrated` |
| 10 | the projector is a legal expressible feature of rank `≤ n`, with exact rational semantics — **given a max–min representation as data** | `ProjectionCompiler.repEF_rank_le`, `repEF_denote`, `repEF_denoteRat`, `projectionStrategy_realizes` |
| 11 | the enforcer is finite data, and its type forbids it seeing the day's price | `ProjectionEnforcer.ProjectionSchedule.enforcer`, `ProjectionScheduleComputation` |
| 12 | the compiled trades are the projection position at the calibrated intensity | `ProjectionEnforcer.ProjectionSchedule.enforcer_realizes` |
| 13 | the paper-facing budget: `−Σ_{k≤n} (ρ_k/δ_k)·d₂(w,K_k)`, no free intensity, no nesting | `ProjectionCalibrated.cumValue_ge_of_calibrated` |
| 14 | per-date admission gives zero risk capital; admission at the last date does not | `ProjectionCalibrated.cumValue_nonneg_of_calibrated`, `ProjectionBudget.late_admission_is_not_enough` |
| 15 | the modified recurrence's bounded evaluator is sound and complete | `EnforcedComputation.enfPrefixFromStagesAtFuel_sound`, `exists_enfPrefixAtFuel` |
| 16 | **the modified market is computable** — no `ComputableMarket` premise | `EnforcedCompiler.computableMarket` |
| 16b | traderized deduction with an effective enforcer is a logical inductor, in the source's *original* sense, with no computability premise | `EnforcedCompiler.isLogicalInductor` |
| 17 | **the theorem of record**, from effective data alone: source-original LIC + per-date Euclidean conformance + the `ℓ^∞` form | `EnforcedCompiler.ProjectionSchedule.end_to_end_effective` |
| 18 | eventual coherence on every fixed finite set | `ProjectionEnforcer.ProjectionSchedule.eventual_coherence` |
| 19 | `ℓ^∞` follows from Euclidean at the same tolerance | `ProjectionForce.sup_conformance_of_dist2` |
| 20 | **homothetic core**: an `α_n`-fraction of every live direction gives `Val_w ≥ −((1−α_n)/α_n)ρ_n`, with **no tolerance penalty** | `ProjectionCore.core_day_value_ge`, `core_day_value_ge_calibrated` |
| 21 | `α = 1` is exactly world-inclusivity, so the hierarchy is continuous | `ProjectionCore.homotheticCore_one_iff` |
| 22 | an inequality constraint can have a positive core; an equality constraint cannot | `ProjectionCore.halfSpace_hasCore`, `equalityRegion_hasNoCore` |

Line 17 is the paper's headline. Its conclusion is the source's `IsLogicalInductor`, not
the generalized criterion.

## 2. What can now be claimed more strongly than the draft claims

* **The conformance conclusion.** `d₂(P_t|_{Φ_t}, Q_t) ≤ δ_t` in place of `d_∞ ≤ δ_t`.
  Strictly stronger at the same `δ_t`; the draft's `ℓ^∞`/`∃μ_t` form is a one-line
  corollary.
* **The opposition constant.** `M_t` disappears in favour of the computable syntactic
  `A_t = tradeListAbsBound(τ_t)`. This strengthens §6.4 for the row route as well.
* **The zero-risk-capital hypothesis.** Per-date admission replaces world-inclusivity plus
  global nesting. Strictly weaker hypothesis, same conclusion.
* **The prospective charge.** Presentation-free, and with the draft's unspecified
  "temporal compatibility" side condition removed rather than restated. See §4.
* **The computability premise.** Gone, and the compiler that replaced it is built. The
  paper can state Theorem 10.6 with effective source data and no `ComputableMarket`
  hypothesis. See §6.
* **The cube hypothesis.** Discharged rather than assumed, from the region lying in the
  cube on the fragment plus the market's own prices lying in the cube.

## 3. What is still conditional, and on what exactly

**One mathematical item.** That each coordinate of `p ↦ proj_{Q_t}(p)` admits a max–min
representation over rational affine forms, and that such a representation is *obtainable*
from a rational description of the region. Conditional on:

1. *Ovchinnikov, "Max–min representation of piecewise linear functions", Beiträge zur
   Algebra und Geometrie 43 (2002) 297–302, Theorem 4.1(a)* — read and quoted in
   `DECISION_MEMO.md §C`, with Definition 2.1's exact notion of piecewise linear and the
   source's own observation that such functions are automatically continuous.
2. The active-set description of the polyhedral projector, written out in
   `COMPUTABILITY.md §1`.

Neither is an axiom. The Lean development takes the representation as **data** and its
correctness as a **hypothesis** (`hrep` in `ProjectionSchedule.end_to_end`), and proves
everything on this side of it.

**No engineering item remains in Debt B.** The bounded-evaluator compiler is built; see §6.

## 4. The cleanest trader-budget statement

Fix a fragment schedule `Φ_t`, regions `Q_t ⊆ [0,1]^{Φ_t}` nonempty closed convex,
positive rational tolerances `δ_t`, and the **calibrated** intensities

```
ρ_t = ε_t + A_t,        λ_t = ρ_t / δ_t².
```

Let `E` be the projection enforcement trader. Then for every point `W` and every horizon
`n`,

```
NW_n(E, P, W)  ≥  − Σ_{k ≤ n} (ρ_k / δ_k) · d₂(W|_{Φ_k}, Q_k).
```

Consequently `E` has assessed downside bounded by

```
B = sup_n sup_{W ∈ S_n} Σ_{k ≤ n} (ρ_k / δ_k) · d₂(W|_{Φ_k}, Q_k),
```

and `B = 0` exactly when every world assessed at a horizon was admitted by every region up
to that horizon. No nesting, monotonicity or temporal-compatibility hypothesis appears, and
no presentation of any region appears.

**A correction to the previous version of this document.** It wrote the day charge as
`λ_k δ_k d₂(·) = (ρ_k/δ_k) d₂(·)` under the hypothesis `λ_k ≥ ρ_k/δ_k²`. That equality is
false under a mere lower bound — under `λ_k ≥ ρ_k/δ_k²` one has `λ_k δ_k ≥ ρ_k/δ_k`, so
the general theorem's bound is *weaker*, not equal. The equality holds exactly at the
calibrated value, which is why the paper's construction must fix `λ_t = ρ_t/δ_t²` rather
than merely bound it below. `ProjectionCalibrated.calibratedIntensity_mul` is the
statement, and its docstring says so. The general free-`λ` theorem
(`ProjectionBudget.cumValue_ge_of_projection`) is retained as a supporting result and is
not weakened.

## 4b. The preservation hierarchy

The paper should present four levels, in order of strength of hypothesis. The point of the
progression is that it is a continuum between an arbitrary convex constraint and the
zero-liability deductive case.

1. **Preservation under bounded plausible downside** — the abstract criterion. Any added
   trader whose cumulative assessed value is bounded below leaves the criterion intact.
2. **Generic projection liability** — for arbitrary convex `K_n`, calibrated enforcement
   charges `(ρ_n/δ_n)·d₂(W|_{Φ_n}, K_n)` per date. This measures *how strongly the
   constraint excludes possibilities that remain live*, and it deteriorates like `1/δ_n`
   as tighter enforcement is demanded.
3. **Homothetic-core refinement** — if there are `c_n ∈ K_n` and `0 < α_n ≤ 1` with
   `c_n + α_n(P_n − c_n) ⊆ K_n`, where `P_n` is the live possibility region on `Φ_n`, then

   ```
   Val_W(E_n) ≥ − ((1 − α_n)/α_n) · ρ_n      for every live W,
   ```

   **independently of `δ_n`.** This measures *whether the constraint retains a uniformly
   positive amount of movement toward every live possibility*. A positive core therefore
   makes arbitrarily precise enforcement possible with no precision-dependent increase in
   the per-date certificate.
4. **World-inclusive / deductive** — if every live world's restriction is itself admitted,
   the liability is exactly zero. This is the `α_n = 1` case of 3.

**What 3 does not give.** A positive core at every date does **not** bound cumulative
liability: `Σ_n ((1−α_n)/α_n)ρ_n` is free to diverge. Indefinite preservation still needs
a separate summability or uniform-bound argument, and
`ProjectionCore.core_netWorth_ge_of_summable` takes that bound as a hypothesis rather than
deriving it. Nor does 3 say that half-spaces automatically get a core depending only on
dimension: `α_n` measures actual geometric slack against the possibility region.

Four conditions that must be kept apart, since they are not equivalent: a pointwise core at
each live world; a core relative to the convex hull of the live restrictions; an ambient
full-dimensional interior condition; and a cumulative bounded-liability condition. The Lean
theorem consumes the first, which is the weakest.

## 5. Computational cost, stated

Effective, not efficient, and the honest form is weaker than "exponential in the fragment
dimension": vertex enumeration, active-set enumeration and max–min expansion each carry
their own blow-up and compound, and obtaining an inequality description from a vertex list
is itself facet enumeration. No single closed-form bound over the composite is claimed.
What the paper needs is computability. Details in `COMPUTABILITY.md §6`.

## 6. Debt B

**Discharged.**

`ComputableMarket` is no longer a premise anywhere in the chain, and the object that
replaced it — `EnforcedBoundedEvaluatorCompiler`, the analogue of the source's own
`LIABoundedEvaluatorCompiler` — is now constructed rather than assumed
(`EnforcedCompiler.compiler`). The blocker was that three ingredients were `private` in the
pinned dependency; the dependency is now pinned to a revision that re-exports them in a
purely additive public section, and `EnforcedCompiler` runs the source's own
primitive-recursion argument with one extra list append.

What the paper may therefore state, with no computability hypothesis: for a computable
deductive process and an enforcer given as effective data, the modified market is computable
and is a logical inductor **in the source's original sense**.

One hypothesis remains and it is not a hidden premise: `Primrec₂ E.trades`, carried by
`EffectiveEnforcerComputation`. That is the definition of "effective enforcer", sitting
exactly where `DeductiveProcessComputation` sits upstream. Establishing it for the
*projection* schedule specifically is the one bounded, mechanical item still open;
`COMPUTABILITY.md §7` says exactly what it needs.

## 7. Re-check of the whole chain

Against the dispatch's verification list, item by item.

| item | status |
| --- | --- |
| nonemptiness of the deductive finite region | **a hypothesis, not proved here.** `K_n` is nonempty iff `D_n` is propositionally consistent. In the Lean it enters only through `IsNearestPoint`, whose first component asserts `K q`; supplying `q` supplies nonemptiness. If a `DeductiveProcess` may have inconsistent stages, the paper must say so — see the open item below. |
| effective enumeration of finite deductively plausible truth patterns | **not formalized.** Decidable in principle; in this development the region enters through the supplied representations, so this sits inside the same §3 gap. |
| exact rationality of all data fed to the compiled trader | **proved.** `FinAffine = List ℚ × ℚ`; `tol : ℕ → ℚ`; `calibratedIntensity` in `ℚ`; `ProjectionCompiler.repEF_denoteRat`. |
| positivity and computability of `δ_n`, `λ_n` | **proved.** `ProjectionSchedule.tol_pos`, `ProjectionCalibrated.calibratedIntensity_pos`; both `ℚ`-valued `def`s; `ProjectionScheduleComputation` states the schedule's effectiveness and typechecks. |
| rank discipline of the day-`n` strategy | **proved.** `EffectiveEnforcer.rank_le`, discharged by `ProjectionCompiler.coefEF_rank_le`. |
| the enforcer does not inspect the day-`n` price except through expressible features | **structural.** `trades : ℕ → List (EF × Sentence) → List (EF × Sentence)` has no price argument; the price enters only when the market maker evaluates `EF.price φ n`. |
| the ordinary `absBound` is computed before the day's fixed point | **structural**, same reason: it is a function of the ordinary trade list's syntax. |
| the market satisfies the source's `ComputableMarket` | **proved from the compiler.** `EnforcedComputation.EnforcedBoundedEvaluatorCompiler.toComputableMarket` produces the source's own definition. |
| exhaustion plus `δ_n → 0` gives eventual coherence on a fixed finite set | **proved.** `ProjectionEnforcer.ProjectionSchedule.eventual_coherence`. |

**The one item that turned up a genuine boundary** is the first. The development never
needs `K_n ≠ ∅` as a separate hypothesis because `IsNearestPoint` carries `K q`; but the
paper, which asserts `Q_t^D = conv(PC(D_t)|_{Φ_t})` and then projects onto it, does need
`PC(D_t) ≠ ∅`, i.e. that the deductive process's stages are consistent. That should be
stated in the paper as a standing hypothesis on `D` rather than left implicit.

## 8. Should `DistanceComplete` be finished, demoted, or abandoned?

**Demoted** — the author's decision, and the mathematics supports it. It is no longer
needed: the `ℓ^∞` conclusion follows from the Euclidean theorem at the same tolerance. It
is not wrong: the exact finite dual presentation was derived and checked exhaustively
against an independent distance program on rational grids in the previous round; what is
missing is the separation direction in the kernel. It answers a real question — the
intrinsic `ℓ^∞` content of a row presentation — that the projection route sidesteps rather
than settles. Keep the results, move them to a section about `ℓ^∞` and row presentations,
mark Theorem 9.3's separation direction as open, and remove Debt A from §12's critical
path.

## 9. What the next step is

The next task is a fresh paper draft built around the chain in §1. Two items should go in
before anything else, because they close gaps rather than strengthen results and they bear
on the row version of the paper as much as on the projection one: the cube extension that
discharges §6.4's contract hypothesis, and the per-date quantifier in §8.1. Then §8.3
becomes §4 above, §9 is demoted, §10.6 is restated over `d₂` with the `ℓ^∞` form as a
corollary, §12's Debt A is removed and Debt B is restated as the upstream hook, and §12's
theorem surface is regenerated from `THEOREM_MAP.md`.


---

## 10. Closure audit — every hypothesis of the current headline theorem

The closure pass is graded against this list. For each hypothesis of
`EnforcedCompiler.ProjectionSchedule.end_to_end_effective`, one of three verdicts:
**(1)** mathematical input the paper genuinely intends to assume; **(2)** an implementation
witness that ought to be constructed; **(3)** a missing theorem wearing a hypothesis as a
disguise. Categories 2 and 3 must not survive into the final paper-facing theorem.

| hypothesis | verdict | disposition |
| --- | --- | --- |
| `process : DeductiveProcessComputation DP` | **(1)** | keep — the paper assumes a computable deductive process |
| `hE : EffectiveEnforcerComputation S.enforcer` | **(2)** | construct from the schedule's computability |
| `K : ℕ → (Sentence → ℝ) → Prop` (free region family) | **(2)** | define from `region n : RationalPolytope` |
| `hlocal : FragmentLocal …` | **(2)** | becomes a theorem about the defined region |
| `hKcube : K n y → … ∈ [0,1]` | **(2)** | becomes a theorem, from the polytope's cube containment |
| `q : ℕ → Sentence → ℝ` (free target family) | **(2)** | define as `proj_{K n}(P_n)` |
| `hq : IsNearestPoint …` | **(2)** | becomes a theorem — nearest-point existence and uniqueness |
| `hrep : repEval … = q n φ` | **(3)** | **this is the disguise.** It asserts that the supplied max–min representation computes the projector, which *is* the polyhedral-projection theorem plus the max–min theorem. Discharged only by formalizing both and generating the representation. |
| `hadm : plausible worlds are admitted` | **(1)** generic, **(2)** deductive | keep in the generic theorem — it is the real assumption that buys zero liability; discharge in the deductive corollary, where the region is defined as the hull of the plausible restrictions |

The schedule's own `reps : ℕ → List FinRep` field is likewise **(2)**: supplying the
compiled representation as data is the artifact §IV removes, replaced by
`region : ℕ → RationalPolytope`.

**Score at the start of the closure pass:** one hypothesis in category (1) unconditionally,
one in (1) for the generic theorem only, six in (2), and one in (3). The single category-(3)
item is `hrep`, and it is the reason the pass exists.
