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

**Proved for the new parts; unchanged and still open for the old part.**

Computable: the fragment schedule; the region as a rational polytope read off the
finite deductive state restricted to the fragment; the max–min representation, by
enumerating active sets; `ε_n = marketMakerError n` and `A_n = absBound`, both
`ℚ`-valued computable functions in the pinned source; hence `λ_n = (ε_n + A_n)/δ_n²`;
hence the compiled `EF`, which is a `def`; and its exact evaluation at the displayed
rational prices by `EF.denoteRat`.

Not closed, and **not made worse by the projection**: `ComputableMarket (history DP E)`
remains an explicit premise, exactly as in the row route. This is the paper's Debt B,
and the projection changes nothing about it — the modified market's computability is a
statement about the market maker's fixed point, not about which trader was added.

`EfficientlyComputable` constrains the traders that attempt exploitation, not the
enforcement trader, so the exponential piece count does not conflict with any
hypothesis of the criterion. It does mean the modified market is computable and not
efficiently computable, which is the paper's own §10.2 disclaimer and is now attached
to a specific exponential rather than to a general worry.

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
2. **Debt B.** `ComputableMarket` for the modified recursive market. Unchanged by this
   pass.
3. **Efficiency.** Nothing here says the enforcement trader is efficient, and the
   piece count says it is not. If a paper claim needs an efficient intrinsic enforcer,
   that claim is not supported.
4. **Theorem 9.3's separation direction.** Still open, and now optional.
