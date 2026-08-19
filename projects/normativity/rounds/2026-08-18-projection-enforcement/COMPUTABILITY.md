# Computability of the modified construction

What has to be computable for the projection route to be a construction rather than a
description, item by item, with the status of each. The conclusion is that everything
the projection introduces is computable and exponential, and that the one thing that
was open before this pass is open in exactly the same way after it.

## 1. The region and its piecewise-affine projector

Let `Φ_n` be the day-`n` fragment, `d = |Φ_n|`, and let

```
K_n = π_{Φ_n}(C_n) ⊆ [0,1]^d
```

be a nonempty rational polytope, given either by a finite rational vertex list or by a
finite rational inequality description `{x : Ax ≤ b}`. In the deductive case
`K_n = conv(PC(D_n)|_{Φ_n})`, whose vertex list is computed by enumerating the
`2^d` sign patterns on `Φ_n` and keeping those propositionally consistent with the
finite set `D_n` — decidable, and exponential in `d`.

**Each coordinate of `p ↦ proj_{K_n}(p)` is piecewise affine with rational
components.** With `K_n = {x : Ax ≤ b}`, `A`, `b` rational, the projection `q(p)` is
characterised by the KKT conditions

```
q = p − Aᵀ μ,      μ ≥ 0,      A q ≤ b,      μ_i (A_i q − b_i) = 0.
```

Fix an index set `I`. On the set of `p` whose optimal active set is exactly `I`, the
constraints in `I` hold with equality and the rest are slack, so `q(p)` is the
Euclidean projection of `p` onto the affine subspace `{x : A_I x = b_I}`. Choosing a
maximal linearly independent subset `J ⊆ I` of the rows,

```
q(p) = p − A_Jᵀ (A_J A_Jᵀ)^{-1} (A_J p − b_J),
```

an affine map with rational coefficients, since `A_J A_Jᵀ` is a rational invertible
matrix. There are finitely many index sets, the corresponding regions of `p` are
polyhedral, and their closures cover `[0,1]^d`. That is exactly Ovchinnikov's
Definition 2.1 with rational components, so his Theorem 4.1(a) applies coordinatewise
and yields, for each `φ ∈ Φ_n`, a finite family of finite subsets `{S_j}` of the
rational affine components with

```
q(p)_φ = max_j min_{i ∈ S_j} g_i(p).
```

Computing the family is a matter of enumerating the index sets and their regions:
**exponential in `d`, and terminating.** No approximation and no floating point enters
at any step; all the linear algebra is over `ℚ`.

For the general parametric statement see Bemporad, Morari, Dua and Pistikopoulos,
Automatica **38** (2002) 3–20 (the explicit multiparametric-QP solution map);
Rockafellar and Wets, *Variational Analysis*, §12.E; Scholtes, *Introduction to
Piecewise Differentiable Equations*, Springer 2012, §2.2.

## 2. The intensity

```
ε_n = marketMakerError n = 2^{-(n+1)}          (pinned source, a `def` into ℚ)
A_n = Strategy.absBound (ordinary aggregate)   (pinned source, a `def` into ℚ)
λ_n = (ε_n + A_n) / δ_n²
```

`absBound` is structural recursion over the expressible feature's syntax; it does not
look at any price. Both quantities are therefore available **before** day `n`'s price
is displayed, which is what makes `λ_n` a legal input to the day-`n` strategy rather
than a circular one. Given a computable rational tolerance schedule `δ_n > 0`, the
intensity schedule is computable in `ℚ`.

## 3. The compiled strategy

`ProjectionCompiler.projectionStrategy` is a `def`, not a `noncomputable def`. Given
the fragment as a duplicate-free list and the representations as data, it produces a
`Strategy n` whose trades are expressible features of rank `≤ n`
(`coefEF_rank_le`, discharged in the `Strategy` field) with support exactly the fragment
(`projectionStrategy_support`).

That the file compiles as executable code is a real check and not a formality. An
earlier draft carried the fragment as a `Finset` and reached for `Finset.toList`, which
is noncomputable in mathlib; Lean rejected every definition downstream of it. The
fragment is now a `Fragment` structure carrying `coords : List Sentence` together with
`nodup`, and `Fragment.sum_eq` bridges list sums to `Finset` sums via
`List.sum_toFinset` so the statements can still be phrased over `Finset`s.

## 4. Exact evaluation

The market's displayed prices are exactly rational, and the compiled term is evaluated
by the source's `EF.denoteRat` in `ℚ`. `repEF_denoteRat` proves that this rational
evaluation agrees term by term with the real denotation used in the theorems, so
nothing is lost between what is proved and what would be run.

## 5. Cost

| object | size |
| --- | --- |
| deductive vertex list `PC(D_n)|_{Φ_n}` | up to `2^{|Φ_n|}` |
| active-set index sets | up to `2^{#rows}` |
| max–min family per coordinate | up to `2^{#components}` |
| compiled `EF` per priced sentence | proportional to the family |
| evaluation of the compiled term | linear in its size, exact in `ℚ` |

The construction is computable. It is not efficient, and no claim here says otherwise.
`EfficientlyComputable` in the criterion constrains the traders that attempt to
exploit the market, not the enforcement trader that is added to it, so the exponential
does not conflict with any hypothesis; it is a cost, recorded as one.

## 6. What remains open

`ComputableMarket (history DP E)` — the paper's **Debt B** — is still an explicit
premise of `isLogicalInductor_of_computableMarket` and of everything that consumes it.
The projection changes nothing here: the premise is about the modified market maker's
recursive fixed point being computable to arbitrary precision, and it is insensitive
to which trader was joined into the day's aggregate. Closing it means transcribing the
source-style first-order compiler and erasure argument for the modified recursion,
which is a separate piece of work of the same size as it was before this pass.
