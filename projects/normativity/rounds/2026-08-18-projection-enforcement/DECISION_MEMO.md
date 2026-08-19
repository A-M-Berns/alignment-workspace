# Decision memo — the projection enforcement trader

The projection trader survives falsification and should become the paper's primary
construction. The row construction stays in the paper as the worked special case and
as the source of the presentation-dependence result; it is not deleted and no theorem
about it is weakened.

Four things had to be true for that verdict, and all four are now checked in the
kernel rather than argued:

1. the force inequality follows from the variational inequality alone — no separation
   theorem, no duality, no net, no row presentation;
2. the comparison point may be chosen *after* the price is displayed, because the
   market maker's daily contract holds at every point of the cube, not only at worlds;
3. the external opposition bound `M_n` is not needed — the source's own syntactic
   `Strategy.absBound` supplies it;
4. the paper's `ℓ^∞` coherence conclusion follows from the Euclidean one **with the
   same tolerance**, so the exact dual-distance presentation is no longer load-bearing
   for the headline theorem.

Point 4 is the one that changes the paper: **Debt A is no longer on the critical
path.**

**Closeout pass, 2026-08-18.** The author has settled the direction: projection is the
paper's main construction, rows are the secondary special case, `DistanceComplete` is off
the critical path, and the canonical construction uses the *calibrated* intensity
`λ_n = ρ_n/δ_n²` rather than any larger value. Three things changed as a result.

* The paper-facing budget now carries no free intensity: the day charge is
  `(ρ_n/δ_n)·d₂(W|_{Φ_n}, K_n)` (`ProjectionCalibrated.cumValue_ge_of_calibrated`). The
  identity `λ_nδ_n = ρ_n/δ_n` holds **only** at the calibrated value, which an earlier
  draft of `PAPER_CLOSURE.md` got wrong; the correction is recorded there.
* The cube extension is explicit. The point fed to the market maker's contract is the
  fragment target extended off the fragment by the displayed prices; it is a device for one
  inequality and not a credence, and the credal conclusion is about the fragment
  projection only. Making it explicit *discharges* the cube hypothesis rather than
  assuming it.
* **Debt B is reduced to the source's own boundary.** `ComputableMarket` is no longer a
  premise anywhere in the chain. See §F.

Classification of every question the dispatch asked. The four grades are used
literally: *proved* = kernel-checked here with no `sorry` and no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`; *proved conditional on a named standard
theorem* = everything is kernel-checked except one externally published statement,
which is taken as a hypothesis and cited exactly, never as an axiom; *likely but
unresolved*; *false*.

---

## The lead question

**Does the projection trader survive, and should it replace the row arc?**
**Proved, and yes — with one external theorem for the compiler.**

The mathematics of §A, §B, §D and §E is unconditional. §C — that the projector can be
written in Logical Induction's expressible-feature grammar — is conditional on
Ovchinnikov's max–min representation theorem, whose exact statement has now been read
and matched to the use (see §C). Everything downstream of the representation is
kernel-checked, including that the compiled term is legal at rank `n`, denotes the
represented value over `ℝ`, computes the same value exactly in `ℚ`, and realizes the
projection position.

The row construction remains valid and is retained. What it loses is the headline
role, for a specific reason: its certified tolerance is presentation-dependent, and
the projection's is not.

---

## A. The projection enforcement theorem

**Proved.**

Convention. Logical Induction values a day's trade at an assessment point `w` as
`Σ_φ shares(φ) · (w φ − P_n φ)` — bought at the displayed price, settled at the
point's payout (`Strategy.value`, pinned source). Write `p = P_n|_Φ`, let `K` be a
nonempty closed convex subset of the fragment's coordinates, `q` the Euclidean
nearest point of `K` to `p`, and

```
ζ = λ · (q − p),        λ ≥ 0.
```

The position points **from the displayed price toward the region**: the trader is
long exactly where the region wants a higher price than the market shows.

The only property of `q` used anywhere is the variational inequality
`⟨p − q, y − q⟩ ≤ 0` for all `y ∈ K` (`ProjectionForce.IsNearestPoint`). From it:

| claim | Lean |
| --- | --- |
| `⟨ζ, y − p⟩ ≥ λ‖q − p‖²` for every `y ∈ K` | `ProjectionForce.force_inequality` |
| `⟨ζ, y − p⟩ ≥ 0` for every `y ∈ K` | `ProjectionForce.value_nonneg_of_mem` |
| `⟨ζ, x − p⟩ ≥ λ(‖q − p‖² − ‖q − p‖ · d₂(x, K))` for every `x` | `ProjectionForce.liability_inequality` |
| with `d₂(p, K) ≤ δ`: `⟨ζ, x − p⟩ ≥ −λ δ d₂(x, K)` | `ProjectionForce.liability_calibrated` |

**May the comparison credence be chosen after seeing `p`? Yes — proved, and this was
the most dangerous circularity in the proposal.** `q` is a function of `p`, so the
market maker's guarantee has to hold at a point that does not exist until the price
does. Two source facts close it. `Strategy.value` is affine in the assessment point
(`Strategy.value_eq_sum_support`), and the market maker's day-`n` contract holds at
every `{0,1}`-valued assignment on the traded support. The unit cube is the convex
hull of those assignments, so the contract holds at every cube point, `q(p)` included
(`ProjectionMarket.value_le_of_forall_bitWorld`,
`ProjectionMarket.marketMaker_day_value_le_cube`). No fixed point is taken twice and
nothing is evaluated before it is defined.

`K` must be nonempty, closed, convex, and contained in the cube; nonemptiness and
cube-containment are explicit hypotheses (`hqcube`), not assumed away.

One detail worth stating because it looks like a hidden falsifier and is not.
`hqcube` asks `0 ≤ q φ ≤ 1` at **every** sentence, not only on the fragment, because the
ordinary aggregate's support need not sit inside the fragment and `Strategy.abs_value_le`
is applied at `q` over that whole support. It is satisfiable: `q` is pinned on `Φ` by the
nearest-point condition and free off it, so taking `q = P` off `Φ` puts `q` in the cube,
and `K` — being a condition on the `Φ`-coordinates, which is what `π_Φ(C_t)` is — admits
that extension. The hypothesis is real and it is cheap; it is not vacuous and it is not
unmeetable.

## B. Eliminating the external bound `M_n`

**Proved.** `ρ_n = ε_n + A_n`, where `ε_n = marketMakerError n` is the market maker's
own slack and `A_n = Strategy.absBound` of the day-`n` ordinary aggregate — a
computable `ℚ`-valued function of that strategy's *syntax*, defined in the pinned
source and evaluated before any price is displayed.

```
λ · ‖q − P_n‖²  ≤  ε_n + A_n                    ProjectionMarket.sqDist_le_slack_add_absBound
λ ≥ (ε_n + A_n)/δ²   ⟹   d₂(P_n|_Φ, K) ≤ δ      ProjectionMarket.dist2_le_of_intensity
```

The previous round's `M_n` was an *assumed* bound on the ordinary traders' opposition.
It is gone. What replaces it is not smaller — `absBound` is a crude syntactic
majorant — but it is derived, computable, and available before the fact, which is what
the finite-time claim needs.

## C. Expressibility of the projection trader

**Proved conditional on a named standard theorem — Ovchinnikov (2002), Theorem 4.1(a),
whose exact statement has been read rather than assumed.**

The dispatch's warning is the right one, so here is the exact version, verbatim from
the source rather than from folklore.

> **Definition 2.1.** Let `Γ` be a closed convex domain in `ℝ^d`. A function
> `f : Γ → ℝ` is said to be *piecewise linear* if there is a finite family `Q` of
> closed domains such that `Γ = ∪Q` and `f` is linear on every domain in `Q`. A
> unique linear function `g` on `ℝ^d` which coincides with `f` on a given `Q ∈ Q` is
> said to be a *component* of `f`.
>
> **Theorem 4.1(a).** Let `f` be a piecewise linear function on `Γ` and
> `{g₁, …, g_n}` be the set of its distinct components. There exists a family
> `{S_j}_{j∈J}` of subsets of `{1, …, n}` such that
> `f(x) = ⋁_{j∈J} ⋀_{i∈S_j} g_i(x)` for all `x ∈ Γ`.

Three things about that statement matter here and all three check out.

* "Linear" means *affine* — the paper says so explicitly: `h(x) = a·x + b`. So the
  components are affine forms, which is what the compiler emits.
* Continuity is **not** an extra hypothesis to discharge: the paper observes that any
  piecewise linear function in the sense of Definition 2.1 is automatically
  continuous.
* `J` may be taken finite, since the `S_j` are subsets of a finite set.

What remains is that each coordinate of `p ↦ proj_K(p)` is piecewise linear on the
cube in exactly that sense, with **rational** components. This is the standard
active-set description of a parametric strictly convex quadratic program, and for this
special case the argument is short enough to write out rather than cite
(`COMPUTABILITY.md`, §1): with `K = {x : Ax ≤ b}` rational, on the set of `p` whose
optimal active set is `I` the projection is
`p ↦ p − A_I^T (A_I A_I^T)^{-1} (A_I p − b_I)` for a maximal independent subset of
`I`, which is affine with rational coefficients; the sets of `p` with a given optimal
active set are polyhedral, finitely many, and their closures cover the cube. Context
for the general parametric statement: Bemporad, Morari, Dua and Pistikopoulos, *The
explicit linear quadratic regulator for constrained systems*, Automatica **38** (2002)
3–20; Rockafellar and Wets, *Variational Analysis*, §12.E; Scholtes, *Introduction to
Piecewise Differentiable Equations*, Springer 2012, §2.2.

**Where the Lean boundary sits.** `ProjectionCompiler` takes the representation as
*data* — a `Fragment` (a duplicate-free list of priced sentences), and per priced
sentence a nonempty list of nonempty groups of rational `AffineForm`s — and its
correctness as a *hypothesis*: `repEval F (R φ) (V n) = q φ`. Everything else is
kernel-checked:

| claim | Lean |
| --- | --- |
| the compiled term is a legal expressible feature of rank `≤ n` | `repEF_rank_le`, `coefEF_rank_le` |
| its real denotation is the represented max–min value | `repEF_denote` |
| its exact rational denotation is the same computation in `ℚ` | `repEF_denoteRat` |
| the compiled coefficients are continuous in the history | `coefEF_continuous` |
| the traded support is exactly the fragment | `projectionStrategy_support` |
| the strategy realizes the projection position | `projectionStrategy_realizes` |
| the compiled strategy is executable code, not a noncomputable definition | `projectionStrategy` is a `def` |

There is no `sorry` and no `axiom` in the file. The last row is not decorative: an
earlier draft routed the fragment through `Finset.toList`, which is noncomputable, and
Lean refused to compile the compiler. Carrying the fragment as a list with a
`Nodup` proof fixed it, and the `def`/`noncomputable def` distinction is now doing
real work as a check on the claim that this is a construction.

**Cost.** The number of pieces — and so the size of the compiled term — is exponential
in the fragment. That is recorded, not hidden; see `COMPUTABILITY.md`.

## D. The intrinsic trader budget, with the quantifiers the general case needs

**Proved, including the negative half.**

```
−Σ_{k ≤ n} λ_k δ_k d₂(w, K_k)  ≤  cumulative value at w        ProjectionBudget.cumValue_ge_of_projection
∀ k ≤ n, w ∈ K_k   ⟹   0 ≤ cumulative value at w               ProjectionBudget.cumValue_nonneg_of_forall_mem
```

No relation between `K_k` at different dates is assumed anywhere — not nesting, not
monotonicity, not eventual stability. The bound is a sum of per-date terms because
that is all a nonmonotone live-world process supports.

The tempting weakening is *false*, and there is a witness:
`ProjectionBudget.late_admission_is_not_enough` exhibits one priced atom, a day-`0`
region excluding the assessed world and a day-`1` region admitting everything, in
which every other hypothesis holds, the world is admitted at the final date, and the
cumulative value is `−1/4`. So "the point ends up admitted" does not bound the budget,
and the paper's statement must carry `∀ k ≤ n`.

The theorems are stated at an arbitrary point of the cube (`cumValue`) and read off at
a world (`netWorth_eq_cumValue`), because the regions are sets of price vectors and
the assessment points are worlds; conflating the two is how the quantifier gets lost.

## E. The deductive specialization

**Proved.**

A deductive process is monotone, so a world plausible at date `n` is plausible at
every earlier date, and the per-date hypothesis of §D follows from the single clause
"every plausible world's payout is admitted by its own date's region". Then:

| claim | Lean |
| --- | --- |
| the day's enforcement value is nonnegative at every plausible world | `ProjectionBudget.deductive_day_value_nonneg` |
| zero risk capital: no efficiently computable trader exploits the modified market | `ProjectionBudget.no_efficient_trader_exploits_of_projection` |
| finite-time Euclidean coherence at every date | `ProjectionBudget.deductive_dist2_le_of_intensity` |
| both at once, plus the paper's `ℓ^∞` form | `ProjectionBudget.deductive_projection_end_to_end` |

The end-to-end theorem's three conjuncts are: no efficiently computable trader
exploits `P^D`; `d₂(P_n|_{Φ_n}, K_n) ≤ δ_n` for every `n`; and there is an admitted
price vector agreeing with the displayed one to within `δ_n` on every sentence of
`Φ_n`. The third is the paper's Theorem 10.6 conclusion in the paper's own `ℓ^∞`
form, and it costs one line — `‖x‖_∞ ≤ ‖x‖_2`
(`ProjectionForce.sup_conformance_of_dist2`).

Nonexploitation reuses the existing `DeductiveEnforcement` chain unchanged; that chain
was already generic in the added trader, so nothing about it had to be re-proved for
the projection route. The row route's theorems still hold.

## F. Computability of the modified construction

**Reduced to the source's own boundary; not closed.**

`ComputableMarket` has been removed as a premise. `EnforcedComputation` introduces an
`EffectiveEnforcer` — a function from the date and the ordinary aggregate's *trade list*
to its own trade list — builds the modified bounded recurrence exactly as the source
builds its own, and proves it monotone in the fuel, satisfiable at some fuel, and **sound**
(every successful bounded run is the semantic construction). Minimizing over the fuel
clock produces the exact rational quote program, so:

| claim | Lean |
| --- | --- |
| the modified market is computable | `EnforcedComputation.EnforcedBoundedEvaluatorCompiler.toComputableMarket` |
| the deductive market is a logical inductor **in the source's original sense**, with no computability premise | `EnforcedComputation.isLogicalInductor_of_compiler_of_worldInclusive` |
| from effective data: source-original LIC + Euclidean conformance + the `ℓ^∞` form | `ProjectionEnforcer.ProjectionSchedule.end_to_end` |
| eventual coherence on every fixed finite set | `ProjectionEnforcer.ProjectionSchedule.eventual_coherence` |

`ProjectionEnforcer` supplies the effective input interface: `FinAffine = List ℚ × ℚ`
rather than a function on sentences, so the schedule is finite data and every type in it is
`Primcodable` from the pinned dependency's public instances.
`ProjectionScheduleComputation` states the requirement and typechecks.

Two facts fall out of the *type* rather than needing an argument: the enforcer cannot
inspect the day's price (its arguments are the date and a trade list), and `absBound` is
therefore computed before the day's fixed point.

**What is left** is one object, `EnforcedBoundedEvaluatorCompiler` — the analogue of the
source's own `LIABoundedEvaluatorCompiler`. It is not discharged because three lemmas
needed for it are `private` in the pinned dependency: `marketMakerSearchUpToTradeList_prim`
(`LIACompiler.lean:4804`), `tradingFirmTradesFromStageTradeLists_prim` (6960), and
`efAbsBound_prim` (6254); that file has 398 private declarations and the recurrence-level
entry points sit on top of most of them. The route to closure is an upstream change — give
the erased recurrence a `Primrec₂` trade-list hook, of which ordinary LIA is the empty
instance — after which the remaining work here is `Primrec₂ S.enforcer.trades`, which is
mechanical. **The obstruction is module visibility and assembly, not mathematics.**
`COMPUTABILITY.md §7` carries the exact ask.

**Cost.** Effective, not efficient. The honest form is weaker than "exponential in the
fragment": vertex enumeration, active-set enumeration and max–min expansion each blow up
and compound, and getting an inequality description from a vertex list is facet
enumeration. No single closed-form bound over the composite is claimed.

## G. Projection versus rows

See `COMPARISON.md`. The short form: rows win on term size and on being
self-contained; the projection wins on everything the paper claims.

| | rows | projection |
| --- | --- | --- |
| certified conformance | in the selected presentation's violations | in the intrinsic Euclidean distance |
| tolerance depends on the presentation | yes — unboundedly | no |
| intensity needed for tolerance `δ` | `β ≥ ρ / (δ² ‖c‖²)`, presentation-dependent | `λ ≥ ρ / δ²` |
| needs a duality/separation theorem to reach a distance | yes (Debt A) | no |
| gives the paper's `ℓ^∞` conclusion | only through Debt A | immediately, same `δ` |
| compiled term size | linear in the number of rows | exponential in the fragment |
| external mathematics required | none | Ovchinnikov Thm 4.1(a) + active-set piecewise affinity |

The two are not rivals at the level of the algebra: for a single halfspace they are
*the same trader*. The projection position at intensity `λ` equals the row position at
`β = λ/‖c‖²` — checked exactly in `tests/test_projection.py`
(`test_single_halfspace_positions_agree`). Rows are the projection specialized to one
constraint at a time and then summed; the sum is what loses intrinsicness.

## H. The rest of the paper

See `PAPER_AUDIT.md`. Nothing in the draft is false; what the audit separates is an
undischarged step in the spine — §6.4's contract hypothesis, which §10.6 instantiates
and nothing discharges — from hypotheses that are simply stronger than the proofs need.
Summary of what this pass changes and what it leaves:

* §9.1 (presentation dependence) — keep, and it is now *motivation for the projection*
  rather than motivation for the dual construction. Exact witness in
  `test_rescaled_rows_shrink_the_violation_without_moving_the_region`.
* §9.2, Lemma 9.2, Theorem 9.3 (`d_∞` duality, nets, exact dual presentation) —
  **demote, do not abandon and do not rush to finish.** They are correct results about
  `ℓ^∞` distance and row presentations, and they are no longer on the path to
  Theorem 10.6.
* Corollary 9.4 — restate over `d₂`, with the `ℓ^∞` form as a corollary.
* Theorem 10.6 — the hypothesis "the day-`t` enforcement trader uses a finite exact
  distance-complete presentation of `Q_t^D`" is replaced by "the day-`t` enforcement
  trader plays the projection position onto `Q_t^D` at intensity
  `λ_t ≥ (ε_t + A_t)/δ_t²`". The conclusion strengthens from `d_∞ ≤ δ_t` to
  `d₂ ≤ δ_t`, and the paper's boxed `ℓ^∞`/`∃μ_t` form survives verbatim.
* §12 Debt A — **remove from the critical path**; it becomes an open question about
  the `ℓ^∞` theory, not a debt of the main theorem.
* §12 Debt B — unchanged.

---

## What is still not proved

1. **The two external facts of §C.** Ovchinnikov Theorem 4.1(a) is published and its
   exact statement has been matched to the use; the active-set piecewise affinity of
   the projector is standard and written out but not formalized. A Lean proof of
   either is a substantial development (polyhedral geometry, hyperplane arrangements)
   and was not attempted here.
2. **Debt B, the remaining sliver.** The bounded-evaluator compiler. Reduced from "assume
   the market is computable" to one `Computable₂` statement about a bounded evaluator,
   blocked on three `private` lemmas upstream. Engineering, not mathematics — see §F.
3. **Efficiency.** Nothing here says the enforcement trader is efficient, and the cost
   analysis says it is not. If a paper claim needs an efficient intrinsic enforcer, that
   claim is not supported.

5. **Nonemptiness of the deductive region.** The Lean never needs it separately, because
   `IsNearestPoint` carries `K q`. The paper does: `Q_t^D = conv(PC(D_t)|_{Φ_t})` is a
   region only if `PC(D_t) ≠ ∅`. That should be a standing hypothesis on `D` rather than
   left implicit.
4. **Theorem 9.3's separation direction.** Still open, and now optional.
