# Paper closure report

What the strongest defensible version of *Generalizing and Strengthening Logical
Induction* now is, what construction realizes it, and what hole is left.

## 1. The recommended theorem chain

Each line names the Lean declaration that is the statement of record. Everything below
is kernel-checked with no `sorry` and axioms `[propext, Classical.choice, Quot.sound]`
only, except where a hypothesis is explicitly named as external.

| # | claim | statement of record |
| --- | --- | --- |
| 1 | Logical Induction's construction consumes an assessment (support) process, not deduction | `AssessmentFirm.*`, `AssessmentProperties.*` (merged) |
| 2 | the generalization is proper | `AssessmentProperties.allTrueLive_not_deductive` (merged) |
| 3 | a strategy's day value is bounded on the whole price cube, not only at worlds | `ProjectionMarket.value_le_of_forall_bitWorld`, `ProjectionMarket.marketMaker_day_value_le_cube` |
| 4 | the projection position forces the price toward the region: `λ‖q−P‖² ≤ ⟨ζ, y−P⟩` for `y ∈ K` | `ProjectionForce.force_inequality` |
| 5 | its value is nonnegative at every admitted point | `ProjectionForce.value_nonneg_of_mem` |
| 6 | its liability anywhere is `≥ −λ δ d₂(w, K)` once the price conforms to `δ` | `ProjectionForce.liability_calibrated` |
| 7 | the intensity that buys tolerance `δ` is `λ ≥ (ε_n + A_n)/δ²`, with no assumed `M` | `ProjectionMarket.sqDist_le_slack_add_absBound`, `ProjectionMarket.dist2_le_of_intensity` |
| 8 | the projector is a legal expressible feature of rank `≤ n`, with exact rational semantics — **given a max–min representation as data** | `ProjectionCompiler.repEF_rank_le`, `repEF_denote`, `repEF_denoteRat`, `projectionStrategy_realizes` |
| 9 | the cumulative budget is `−Σ_{k≤n} λ_k δ_k d₂(w, K_k)`, with no nesting hypothesis | `ProjectionBudget.cumValue_ge_of_projection` |
| 10 | per-date admission gives zero risk capital, and admission at the last date does not | `ProjectionBudget.cumValue_nonneg_of_forall_mem`, `ProjectionBudget.late_admission_is_not_enough` |
| 11 | traderized deduction keeps the original criterion and is finite-time coherent, in `d₂` and in `ℓ^∞` | `ProjectionBudget.deductive_projection_end_to_end` |
| 12 | the `ℓ^∞` conclusion follows from the Euclidean one with the same `δ` | `ProjectionForce.sup_conformance_of_dist2` |

Line 11 is the paper's headline (Theorem 10.6) and it now has three conjuncts rather
than two.

## 2. What can now be claimed more strongly than the draft claims

* **The conformance conclusion.** `d₂(P_t|_{Φ_t}, Q_t) ≤ δ_t` in place of
  `d_∞(P_t|_{Φ_t}, Q_t) ≤ δ_t`. Strictly stronger at the same `δ_t`; the draft's boxed
  `ℓ^∞`/`∃μ_t` form is a one-line corollary.
* **The opposition constant.** `M_t` disappears in favour of the computable syntactic
  `A_t = absBound(τ_t)`. This strengthens §6.4 for the row route as well.
* **The zero-risk-capital hypothesis.** Per-date admission replaces world-inclusivity
  plus global nesting. Strictly weaker hypothesis, same conclusion.
* **The prospective charge.** `q_t = ρ_t d₂(W|_{Φ_t}, Q_t)/δ_t` with
  `B = sup_n sup_{W ∈ S_n} Σ_{k≤n} q_k(W)`, presentation-free, and with the draft's
  unspecified "temporal compatibility" side condition removed rather than restated.
* **The intensity.** `λ_t ≥ ρ_t/δ_t²` for every presentation of every region, against
  the row route's presentation-dependent `β_j ≥ ρ_t/(δ_t²‖c_j‖²)`.

## 3. What is still conditional, and on what exactly

**One item.** That each coordinate of `p ↦ proj_{Q_t}(p)` admits a max–min
representation over rational affine forms. Conditional on two published statements,
neither introduced as an axiom:

1. *Ovchinnikov, "Max–min representation of piecewise linear functions", Beiträge zur
   Algebra und Geometrie 43 (2002) 297–302, Theorem 4.1(a)* — read and quoted in
   `DECISION_MEMO.md §C`, with Definition 2.1's exact notion of piecewise linear (a
   finite family of closed domains covering a closed convex `Γ`, affine on each) and
   the observation, in the source, that such functions are automatically continuous.
2. The active-set description of the polyhedral projector, written out in
   `COMPUTABILITY.md §1` — elementary, and cited for context to Bemporad–Morari–Dua–
   Pistikopoulos (2002), Rockafellar–Wets §12.E, and Scholtes (2012) §2.2.

Given the representation, everything else about the compiler is kernel-checked,
including that the compiled strategy is *executable code* rather than a noncomputable
definition.

The paper should state this boundary rather than blur it: the enforcement trader's
legality rests on a cited classical representation theorem, and the artifact proves
everything on this side of it.

## 4. The cleanest trader-budget statement

Fix a fragment schedule `Φ_t`, regions `Q_t ⊆ [0,1]^{Φ_t}` nonempty closed convex,
tolerances `δ_t > 0`, and intensities `λ_t ≥ ρ_t/δ_t²` where `ρ_t = ε_t + A_t`. Let `E`
be the projection enforcement trader. Then for every world `W` and every horizon `n`,

```
NW_n(E, P, W)  ≥  − Σ_{k ≤ n} λ_k δ_k d₂(W|_{Φ_k}, Q_k)
               =  − Σ_{k ≤ n} ρ_k d₂(W|_{Φ_k}, Q_k) / δ_k .
```

Consequently `E` has assessed downside bounded by

```
B = sup_n sup_{W ∈ S_n} Σ_{k ≤ n} ρ_k d₂(W|_{Φ_k}, Q_k) / δ_k ,
```

and `B = 0` exactly when every world assessed at a horizon was admitted by every region
up to that horizon. No nesting, monotonicity or temporal-compatibility hypothesis
appears, and no presentation of any region appears.

This is the statement to put in the paper. It is one formula, it is intrinsic, and it
specializes to the deductive `B = 0` by monotonicity of `D`.

## 5. Computational cost, stated

Computable, exponential, and not efficient. Per date: up to `2^{|Φ_t|}` candidate
vertices for a deductive region, up to `2^{#rows}` active sets, and a max–min family
whose size is bounded by the number of pieces. Evaluation of the compiled term is
linear in its size and exact in `ℚ`. `EfficientlyComputable` constrains the traders
that attempt to exploit the market, not the enforcement trader, so nothing here
conflicts with a hypothesis — it is a cost. Details in `COMPUTABILITY.md §5`.

## 6. Should `DistanceComplete` be finished, demoted, or abandoned?

**Demoted.** Not abandoned, and not finished at any cost.

* It is no longer needed. The `ℓ^∞` conclusion the paper wants follows from the
  Euclidean theorem with the same tolerance, so nothing in the headline chain routes
  through the exact dual-distance presentation.
* It is not wrong. The exact finite dual presentation `N*(V) = ⋃_v vert(R_v)` was
  derived and checked exhaustively against an independent distance program on rational
  grids in the previous round. What is missing is the separation direction in the
  kernel.
* It answers a real question — *what is the intrinsic `ℓ^∞` content of a row
  presentation* — that the projection route sidesteps rather than settles.

So: keep the results, move them into a section about `ℓ^∞` and row presentations, mark
Theorem 9.3's separation direction as open, and remove Debt A from §12's critical path.
If someone later wants the `ℓ^∞` distance itself rather than a bound on it, the work is
there and unspoiled.

## 7. Remaining holes, in order of how much they cost

1. **Debt B — `ComputableMarket` for the modified recursive market.** Unchanged by this
   pass, still an explicit premise. This is the one hole that stands between the paper
   and an unconditional Theorem 10.6, and it was already the case before the projection
   entered.
2. **The representation theorem of §3 above.** External, published, exact statement
   matched to the use. Formalizing it means hyperplane arrangements and polyhedral
   geometry in Lean; it is a project, not a pass.
3. **Theorem 9.3's separation direction.** Now optional.
4. **Efficiency.** Nothing supports an efficient intrinsic enforcer, and the piece count
   argues against one. If a claim in the paper needs efficiency, it is not supported.

## 8. What the next step is

Rewrite §§6, 8.3, 9 and 10.6 of the paper against `PAPER_AUDIT.md`, in that order, and
regenerate §12 from `THEOREM_MAP.md`. The two changes that close gaps rather
than strengthen results — the cube extension that discharges §6.4's contract
hypothesis, and the per-date quantifier in §8.1 — should go in first, because they are
load-bearing for both constructions. Neither statement in the draft is false; the chain
simply does not currently discharge what it assumes.
