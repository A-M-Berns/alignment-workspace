# Track B report — finite settlement classification and the local delegation bridge

Stated over **`projects/deference/notes/FINITE_MODEL_SKELETON.md` version `v1`.**
No object is renamed or re-typed. Three deficiencies in v1 were found; minimal
patches are proposed in §9 and none was applied locally. Two objects are *added*
(a one-shot pricing layer, a transfer-bearing valuation variant), named as
additions and listed in §5 and §8.

Notation for a single decision index `n`, all of it v1's:
`W(ω,π) := v⁺_n(ω,π)`, `G(ω) := (W(ω,π))_{π∈Π_n}` (the **grade profile**),
`J := J_n`, `X_π := X_{n,π}`, `P := P_n`, `V := V_n`, `B` the bound.

---

## 1. Exact result

### 1.1 The classification

The decisive fact is one line of v1: **`V_n` is an average of `X` and nothing
else.** Of the three settlement instantiations of §5, only instantiation 2 supplies
a quantity that occurs in the valuation the target inequality is stated in. That is
not a theorem about settlement; it is v1 §6 fixing, by the choice of valuation, most
of what §5 was written to leave open. What is left genuinely open — and is answered
below — is which instantiation can supply the *hypothesis* the bridge needs.

| instantiation | what it yields, exactly | contribution to `V_n(DELEGATE) ≥ V_n(c) − ε` |
|---|---|---|
| 1. grade/report | (i) prediction of `v⁺_n`: A's price is forced into the convex hull of the grades realizable on its current `𝓕_{t(n)}`-cell, and nothing further (P1); (ii) the `F(n)`-observable **comparison** `taken π vs. reported J_n(ω)`, which is the only thing a transfer can be written on | none. `v⁺` enters `V_n` only through the selection `J`; W4 exhibits perfect grade prediction, zero exploitability on grade contracts, and the maximal possible deficit `2B` |
| 2. world/outcome | prediction of the declared `X_{n,π}` in the same hull sense (P1 with `val = X`). It is the only instantiation whose settled values are arguments of `V_n`, and the only one under which the bridge's hypothesis and conclusion are both ex-post measurable, hence falsifiable | supplies the *objects* of the inequality; supplies no *link* between `X` and `v⁺`, and the link is the entire content (T1, T3) |
| 3. underwriting/enforcement | enforced conformity, with **zero epistemic content**: T5(b) holds for every instance of the skeleton — every `X`, every `P`, every principal, competent or not. Its price is a bond of exactly `2B` per unit of disagreement mass. As typed in v1 it yields nothing at all (T5(a), W3) | delivers the conclusion `V^τ_n(DELEGATE) ≥ V^τ_n(c)` outright, in a valuation that is not v1 §6's |

**The trust relation is imported.** The hypothesis T1 needs (`GT_𝒢(η)`, §1.2) is a
constraint on how the principal's grade tracks the intervention-indexed quantity.
When the conditioning partition is discrete — A and the principal both fully
informed — it reduces to `|X_π(ω) − W(ω,π)| ≤ η` pointwise, a statement containing
no reference to `P` and hence no epistemic content about A whatsoever. No coherence,
no-sure-gain, or exploitability condition on A can establish it, because it is not
about A. It is a competence hypothesis about the principal, and v1 supplies no
mechanism that produces one.

### 1.2 The bridge

*Definition (added, provisional).* A partition `𝒢` of `Ω` is **admissible for `n`**
when it refines `𝓕_{t(n)}` and refines the level sets of `G`. The coarsest is
`𝒢₀ := 𝓕_{t(n)} ∨ σ(G)`; `𝓕_{F(n)}` is admissible, because `v⁺_n` is `F(n)`-measurable
and `𝓕` is nondecreasing in refinement with `t(n) < F(n)`.

*Definition (added, provisional).* **Grade trust at level `η`**, `GT_𝒢(η)`: for every
cell `C ∈ 𝒢` with `P(C) > 0` and every `π ∈ Π_n`,

```
| E_P[ X_π | C ] − W(·,π)|_C |  ≤  η ,
```

`W(·,π)` being constant on `C` since `𝒢` refines `σ(G)`.

*Definition (added, provisional).* **Grade margin** `M(c) := E_P[ W(·,J) − W(·,c) ]`
and **disagreement mass** `D(c) := P({ω : c(ω) ≠ J(ω)})`, for a selection `c`.
`M(c) ≥ 0` by pointwise maximality of `J`, with no hypothesis.

> **T1 (the local delegation bridge).** Assume `GT_𝒢(η)` for an admissible `𝒢`. Then
> for every `𝒢`-measurable selection `c : Ω → Π_n`,
> ```
> V_n(DELEGATE)  ≥  V_n(c)  +  M(c)  −  2·η·D(c) .
> ```
> Equivalently `V_n(DELEGATE) ≥ V_n(c) − ε(c)` with `ε(c) = max(0, 2ηD(c) − M(c))`.

*Proof.* `J` is `σ(G)`-measurable, hence `𝒢`-measurable, so both `J` and `c` are
constant on each cell; write `J(C)`, `c(C)`.
`V_n(DELEGATE) − V_n(c) = Σ_C P(C)·( E[X_{J(C)}|C] − E[X_{c(C)}|C] )`.
A cell with `c(C) = J(C)` contributes exactly `0`. A cell with `c(C) ≠ J(C)`
contributes at least `(W_C(J(C)) − η) − (W_C(c(C)) + η)` by the two directions of
`GT_𝒢(η)`. Summing, and using that `W_C(J(C)) − W_C(c(C)) = 0` on the agreement
cells so that the disagreement cells carry all of `M(c)`, gives
`≥ M(c) − 2ηD(c)`. ∎

Three things about the constant. It is **derived**, not imported: the `2` is the two
one-sided uses of `GT_𝒢`, the `η` is the trust level, the `D(c)` is the measure of
the region where the two conducts actually differ, and `M(c)` is the principal's own
grade margin, which is free. Nothing in the proof is a Total Trust theorem, a
Dutch-book argument, or a limit. And the tolerance is **paid only on the
disagreement region** — the cruder constant `2η` is what one gets by bounding
`D(c) ≤ 1`.

> **T1′ (unconditional).** With no hypothesis, `V_n(DELEGATE) ≥ V_n(c) − 2B·D(c)`,
> since `|X| ≤ B`. Combining: `ε(c) = min( 2B·D(c), max(0, 2ηD(c) − M(c)) )`.

> **T1″ (the comparator dial).** If `𝒢'` refines `𝒢` and both are admissible then
> `GT_{𝒢'}(η) ⇒ GT_𝒢(η)`, strictly in general. Refining `𝒢` therefore strengthens
> the hypothesis and widens the comparator class in lockstep: **the class of
> comparators the bridge covers and the strength of the trust relation are one
> dial.**

*Proof of T1″.* `E[X_π|C]` is a convex combination of `E[X_π|C']` over the `𝒢'`-cells
`C' ⊆ C`, and `W(·,π)` is the same constant on all of them. Strictness: W1 (§6)
satisfies the coarser relation at `η = 0` and the finer one only at `η = 2`. ∎

**Comparator coverage.** `FIXED[π]` and `SIM` are `𝓕_{t(n)}`-measurable, hence
covered for every admissible `𝒢`. `DELEGATE` is `σ(G)`-measurable. `FU[g]` — v1's
declared hole — is covered exactly when its selection is `𝒢`-measurable; taking
`𝒢 = 𝓕_{F(n)}` covers every comparator whose selection is `F(n)`-measurable, hence
every `FU[g]` with `g(n) ≤ F(n)`, at the cost of `GT_{𝓕_{F(n)}}(η)`, the strongest
member of the family. This is the exact price of reaching Movement IV's comparator,
and it is a price in the trust hypothesis, not in the proof.

### 1.3 What makes disagreement with the principal profitable

The prompt's question, answered exactly. Under `GT_𝒢(η)`, disagreeing with the
principal costs A when `M(c) > 2η·D(c)` — that is, when the principal's grade margin
*per unit of disagreement mass*, `M(c)/D(c)`, exceeds `2η`. The break-even rate is
`2η` and nothing else. So:

1. **Grade/report settlement makes disagreement cost nothing.** It constrains A's
   prices for the grade contracts (P1) and leaves `η` completely free. W4 is the
   sharp case: A predicts the principal's grades perfectly, no position on grade
   contracts has a positive payoff in any state, and the delegation deficit is `2B`
   — the largest the bound `B` permits. Grade settlement's unique force is to drive
   `v̂⁺` toward `v⁺`, which is the definition of *predicting the principal*, and
   under T4 that is precisely the direction of simulator substitution.
2. **World/outcome settlement makes disagreement measurable, not costly.** It makes
   `X` an object A can be scored on; it never compares `X` to `v⁺`, so it cannot
   produce `η`. It does make the bridge falsifiable ex post: `η`, `M(c)` and `D(c)`
   are all `F(n)`-measurable once the relevant `X` settle.
3. **Enforcement makes disagreement costly by fiat.** T5(b) does it with no
   epistemic hypothesis, at bond `2B`, for every instance — and it is the only
   instantiation that reaches decisions whose `X` does not settle.

There is no fourth source in v1. **Under 1–2 nothing makes disagreement
unprofitable; under 3 something does, and it is enforcement.** That is the round's
settlement classification, and it is the "enforcement rather than epistemic trust"
outcome the roadmap said would be a result.

The dependency runs one further step, and it is the architecturally interesting one:
the bond of T5(b) must be paid against the comparison `taken π` vs. `J_n(ω)`, which
is settleable only under instantiation 1. **Grade settlement has no force in the
valuation and is exactly the observable that enforcement needs.** The two
instantiations that yield no delegation compose into the one that does.

### 1.4 The other four statements

> **P1 (what settlement forces on a price).** *Added structure — see §5, A3.* Fix
> `C ∈ 𝓕_{t(n)}` and a settlement instantiation with settleable items `{(n,π)}`.
> Let `ρ ∈ ℚ^{Π_n}` be A's price vector on `C` and a position be any
> `h ∈ ℚ^{Π_n}`, with profit `Σ_π h_π (val_{(n,π)}(ω) − ρ_π)`. No position has
> positive profit at every `ω ∈ C` **iff** `ρ ∈ conv{ (val_{(n,π)}(ω))_π : ω ∈ C }`.
> *Proof.* (⇐) If `ρ = Σ_ω λ_ω v(ω)` then `Σ_ω λ_ω · profit(ω) = 0` for every `h`.
> (⇒) Otherwise separate `ρ` from the rational polytope `conv{v(ω)}` by a rational
> functional `h`, whose profit is uniformly positive on `C`. ∎
> With `val = v⁺` this is *prediction of the principal's grades*; with `val = X` it
> is *prediction of the quantity*. Neither constrains the other, and the joint
> version — pricing both families consistently under one `λ` — constrains only that
> the two prices come from a common measure, which places no bound on
> `|E_λ[X_π] − E_λ[v⁺_π]|` beyond the trivial `2B`.

> **T3 (grade settlement supplies nothing to the bridge).** There is an instance of
> v1 in which `v̂⁺_n = v⁺_n` pointwise, no position on grade contracts profits in any
> state, and `V_n(DELEGATE) = V_n(FIXED[π₁]) − 2B`. Witness W4, §6.

> **T4 (no `DELEGATE`/`SIM` separation in `V_n`).** If `v̂⁺_n = v⁺_n` pointwise then
> `Ĵ_n = J_n` and `V_n(SIM) = V_n(DELEGATE)` exactly. In general T1 gives
> `V_n(DELEGATE) ≥ V_n(SIM) + M(SIM) − 2ηD(SIM)` where
> `M(SIM) = E_P[W(·,J) − W(·,Ĵ)]` is the model's **grade regret**. The whole
> separation between deference and simulation that v1's valuation can express is a
> prediction-quality quantity; the difference in *rule* (§4) contributes exactly `0`
> to `V_n`. Movement III is not addressable inside v1 §6, and this confirms the
> roadmap's standing commitment rather than weakening it.

> **T5 (enforcement).** (a) With `τ : {(n,π)} → ℚ` as typed in v1 §5.3 and the
> transfer-bearing valuation `V^τ_n(c) = Σ_ω P(ω)[ X_{n,c(ω)}(ω) + τ(n,c(ω)) ]`,
> there are instances where **no** `τ` makes `DELEGATE` optimal, even against the
> constant comparators alone. Witness W3, §6; the two required inequalities sum to
> `0 ≥ 2`.
> (b) With the minimal patch `τ : {(n,π,π')} → ℚ` settled at `F(n)` against the
> principal's report `π' = J_n(ω)`, the uniform conformity bond
> `τ(n,π,π') = −λ·1{π ≠ π'}` makes `DELEGATE` `V^τ_n`-optimal against **every**
> conduct iff `λ ≥ 2B`; `2B` is attained (W2). Per instance and uniformly in `P`,
> the minimal bond is `λ* = max_{ω ∈ supp P, π} ( X_{n,π}(ω) − X_{n,J(ω)}(ω) )⁺`.
> (c) T5(b) uses no relation among `X`, `v⁺` and `P`. It holds for every instance of
> the skeleton.

## 2. Evidence class

Nothing here is registered; `CLAIMS.md` does not exist (`CORRIGIBILITY_PAPER_LEDGER.md`,
"the one-line status"). Registration is a maintainer act — §9(3).

| object | class it would support | status now |
|---|---|---|
| T1, T1′, T1″, P1, T3, T4, T5(a) infeasibility, T5(b) | none of the registry classes — a hand proof is not a class in `AGENTS.md` | **proposal**, per `AGENTS.md` standard 3. Lean port is the deliverable that makes them citable (§10) |
| E1, E2 (T1 over a declared `X`-box), W2-necessity, W2-sufficiency, W3-grid | `enumeration-verified` — the house checker in `checkers/enumeration.py` generates the domain itself from the parameters | parameter sets in `certificates.json`; the unmodified house checker accepted all five in this round, outside CI |
| W1, W4, and the T1 sharpness family | `witness-checked` — exact instances, one exact predicate each | recomputed exactly by `verify.py`; not yet cast as `CLAIMS.md` entries |
| exhaustive `GT_marg(0)` deficit maxima at `B = 2, 3` | `enumeration-verified` in substance, **not** in form: the search is contributor code, and the house checker's domains do not generate this family | reported as a computation, not a certificate |

The two enumeration caveats, stated because they are easy to overread. The
`rational-grid` domain is a *lattice* in the hypothesis box, not the box; E1 and E2
verify T1 at the 625 lattice points each. The extension to the whole box is the
one-line convexity argument (the constraint is linear, the box's extreme points are
lattice points), and that argument is part of the hand proof, not part of the
checker's verdict. And every certificate fixes `(Ω, Π, P, v⁺, 𝒢, η)` as structural
data and quantifies only over `X`; T1's quantification over structures is not
certified by them.

## 3. Files, declarations, checks

- `prompts/2026-08-11-deference-finite-kernel/verify.py` — exact-rational model code
  (`fractions.Fraction` throughout, no float appears), recomputation of every
  constant below, and submission of the five certificate parameter sets to the
  unmodified house checker imported from `checkers/`. `python3 verify.py` (~1 s);
  `python3 verify.py --slow` adds the two exhaustive searches (~3 min).
- `prompts/2026-08-11-deference-finite-kernel/certificates.json` — the five
  parameter sets, written by `verify.py`.

Everything `verify.py` asserts, exactly:

```
T1 sharpness           equality at 16 (m, η) pairs, m ∈ {0,1/4,1/2,1}, η ∈ {0,1/8,1/2,1}
W1                     GT_marg level 0; GT level 2; V(DELEGATE) 1/2; V(FIXED[π₀]) 1;
                       M 1/2; D 1/2; deficit 1/2
W1-family              deficit exactly B/2 at B ∈ {1,2,3,5,7/2}, GT_marg level 0
exhaustive (--slow)    max deficit under GT_marg(0) = B/2 at B = 2 and B = 3
W4                     deficit exactly 2B at B ∈ {1,3,7/2}; Ĵ = J
E1                     enumeration PASS, 625 points; (M,D,ε) = (1/2, 1, 1/2); bound
                       attained at a corner (−1/2)
E2                     enumeration PASS, 625 points; (M,D,ε) = (1/4, 1/2, 1/4); bound
                       attained at a corner (−1/4)
W3                     enumeration PASS, 289 points; rows sum to the zero functional
                       with summed rhs 2, i.e. 0 ≥ 2
W2-necessity           enumeration PASS, 8 points (λ ∈ [0, 7/4], every point violates)
W2-sufficiency         enumeration PASS, 625 points; bound attained at a corner (−1)
```

No Lean was written and `lake build` was not run, per the dispatch.

## 4. What was not established

- **T1 and its four companions are not kernel-checked and not registered.** They are
  hand proofs. The proofs are four to six lines each and the port is mechanical, but
  until it happens the correct label is *proposal*.
- **The trust relation is not derived from anything.** `GT_𝒢(η)` is assumed. §1.1
  argues it *cannot* be produced by any of v1's three instantiations under a
  one-shot no-sure-gain condition, and P1 is the exact statement of what those
  conditions do produce — but "cannot be produced by v1" is not "cannot be
  produced", and the mechanism that would produce it (repeated decisions, a market,
  traders) is exactly what v1 §8.3 and §8.6 remove. This is the same standing gap
  the inherited audit records as its central finding, reappearing in the finite
  kernel; it is not closed here and no claim above should be read as closing it.
- **No cross-decision content.** Everything is at one `n`, per v1 §8.6.
- **The `B/2` maximum is not a theorem.** The exhaustive searches cover
  `|Ω| = 2, |Π| = 2, P = (1/2,1/2)`, integer `v⁺` and `X` in `[−B,B]`, at `B = 2, 3`.
  The displayed family attains `B/2` for every rational `B > 0`, so `Ω(B)` is
  established as a lower bound and `B/2` as a maximum only over the searched family.
- **T5(b)'s optimality is over `V^τ_n`, not `V_n`.** That is a different valuation
  from v1 §6, and by v1's own rule a track proving the inequality in another
  valuation has proved a different theorem. It is reported as such, not as the
  target inequality.
- **`SIM` is not distinguished from `DELEGATE`** by anything here; T4 is the negative
  statement, not a separation.
- **P1's separating functional** is taken rational without a written LP-duality
  argument; the standard fact (a rational polytope and a rational exterior point
  admit a rational separator) is used and not proved.

## 5. Assumptions added

Each is stated at the site where it is used and none is folded into a v1 object.

- **A1 — the admissible conditioning partition `𝒢`** and **`GT_𝒢(η)`** (§1.2). The
  substantive hypothesis of T1. Its nonvacuity is discharged by the construction:
  E1 and E2 enumerate 625 inhabitants each of the full hypothesis package.
- **A2 — the transfer-bearing valuation `V^τ_n`** (§1.4, T5). v1 §6's `V_n` has no
  slot for a transfer, so instantiation 3 cannot act on the valuation at all without
  one. Introduced as a named variant, never as a replacement.
- **A3 — a one-shot pricing layer** for P1: a `t(n)`-measurable price vector and an
  arbitrary rational position on the settleable items, with "no sure gain on a
  `𝓕_{t(n)}`-cell" as the no-exploit condition. v1 §8.3 removes the market and the
  traders entirely; without *some* such layer the question "what does a settlement
  instantiation yield" has no formal content inside v1. A3 is the thinnest layer on
  which it has one, and it is deliberately one-shot: it carries no dynamics and
  therefore cannot, and does not, stand in for the trader machinery.
- **A4 — `τ` may be paid on the pair (taken intervention, principal's report).**
  Used only in T5(b); it is the §9(1) patch, and T5(a) is the proof that without it
  instantiation 3 is inert.

## 6. Counterexamples and necessity witnesses

All exact; all recomputed by `verify.py`. `Ω = {a,b}`, `Π_n = {π₀ < π₁}`,
`P = (1/2, 1/2)` unless stated.

**W1 — the profile-refined conditioning in `GT_𝒢` is necessary; the parallel-cut
relation is not enough.** Let `GT_marg(η)` be the per-`π` relation
`|E_P[X_π | v⁺_n(·,π) = s] − s| ≤ η` for every `π` and every attained `s` — the
finite one-decision shadow of threshold Total Trust, and the relation one would
write first. Take `B = 3`, `𝓕_{t(n)} = {Ω}`, `𝓕_{F(n)}` discrete,

```
v⁺: (a,π₀) 1   (a,π₁) 0   (b,π₀) 1   (b,π₁) 2        so J(a) = π₀, J(b) = π₁
X : (a,π₀) −1  (a,π₁) 0   (b,π₀) 3   (b,π₁) 2
```

`GT_marg` holds at `η = 0` **exactly**: the `π₀`-layer is all of `Ω` and
`½(−1) + ½(3) = 1`, and the two `π₁`-layers are singletons matching their grades.
`GT_𝒢` holds only at `η = 2`. Then `V_n(DELEGATE) = 1/2` and
`V_n(FIXED[π₀]) = 1`: a deficit of `1/2` where T1 with `η = 0` would give `0`.
The mechanism is exactly the amplifier obstruction the inherited note records at its
§1.6 — parallel cuts do not probe within a grade layer — here in one decision with
no limits.

Scaling: with `v⁺(a,π₀) = −B`, `v⁺` else `0`, `X = (−B, −B, 0, B)` and `𝒢` discrete,
`GT_marg` holds at `η = 0` and `V_n(FIXED[π₁]) − V_n(DELEGATE) = B/2`, for every
rational `B > 0`. Exhaustive search over `|Ω| = |Π| = 2`, `P = (1/2,1/2)`, integer
`v⁺, X ∈ [−B,B]` finds `B/2` to be the maximum at `B = 2` and `B = 3`. So the
parallel-cut relation at `η = 0` permits a delegation deficit **linear in `B`**.

**W4 — grade settlement contributes nothing (T3), at the maximal rate.** `Ω = {ω}`,
`v̂⁺ = v⁺ = (1, 0)`, so `J = Ĵ = π₀` and no position on grade contracts profits in
any state. `X = (−B, +B)`. Then `V_n(DELEGATE) = −B` and `V_n(FIXED[π₁]) = +B`:
deficit `2B`, the largest `|X| ≤ B` permits. Verified at `B ∈ {1, 3, 7/2}`.

**W3 — v1 §5.3's `τ` cannot enforce delegation (T5(a)).** `B = 2`,

```
v⁺: (a,π₀) 1  (a,π₁) 0  (b,π₀) 0  (b,π₁) 1     so J(a) = π₀, J(b) = π₁
X : (a,π₀) 0  (a,π₁) 2  (b,π₀) 2  (b,π₁) 0
```

`DELEGATE` optimal under `V^τ_n` against the two constant comparators requires
`½(τ₁ − τ₀) ≥ 1` and `½(τ₀ − τ₁) ≥ 1`, whose sum is `0 ≥ 2`. Certified two ways:
algebraically (the rows sum to the zero functional with summed right-hand side `2`)
and by enumeration over `τ ∈ [−4,4]²` at denominator `2`, 289 points, every point
violating at least one requirement.

**W2 — the conformity bond is exactly `2B` (T5(b)).** Necessity: `Ω = {ω}`,
`v⁺ = (1,0)`, `X = (−B, +B)`; `DELEGATE` is `V^τ`-optimal iff `λ ≥ 2B`. Enumeration
over `λ ∈ [0, 7/4]` at `B = 1` finds every point failing. Sufficiency, on a
structural instance with `B = 1` and `λ = 2`: enumeration over the whole `X`-box
`[−1,1]⁴` at denominator `2`, 625 points, all passing, with the bound attained at a
corner.

**S1 — T1's constant is sharp in both terms.** For every rational `m ≥ 0` and
`η ≥ 0`: `Ω = {a,b}`, `𝓕_{t(n)} = {Ω}`, `𝒢 = σ(G)` discrete,

```
v⁺: (a,π₀) 1     (a,π₁) 1−m      (b,π₀) 2     (b,π₁) 2−m
X : (a,π₀) 1−η   (a,π₁) 1−m+η    (b,π₀) 2−η   (b,π₁) 2−m+η
```

satisfies `GT_𝒢(η)` with `η` exactly attained, has `M(FIXED[π₁]) = m`, `D = 1`, and
`V_n(DELEGATE) − V_n(FIXED[π₁]) = m − 2η` **with equality**. Checked at 16 `(m, η)`
pairs. Hence the coefficient `2` on `η` and the coefficient `1` on `M(c)` are both
exact, and no smaller `ε` is available from `(η, M, D)` alone.

**Tightness of the certificates.** E1 (`ε = 1/2`, comparator `FIXED[π₁]`,
`D = 1`) and E2 (`ε = 1/4`, comparator `π₁` on `a` and `π₀` on `b`, `D = 1/2`) both
attain their bound at a corner of the hypothesis box. A certificate whose bound has
slack would verify a weaker statement without saying so; these do not.

**Nonvacuity.** `AGENTS.md`'s Lean regime requires a term inhabiting the full
hypothesis package. Here the inhabitation is by enumeration rather than by a witness
term: E1 and E2 each exhibit 625 instances satisfying every hypothesis of T1
(including a non-constant comparator in E2 and a non-constant grade profile in
both), and S1 exhibits one for every `(m, η)`. No result rests on a degenerate
single-state or constant-grade instance except W4 and W2-necessity, where the point
being made is a maximum and the one-state model is the extremal one.

## 7. Deviations

1. **The dispatch names the parent snapshot as `ec7d6cc`; the checkout is at
   `990a822`.** The skeleton differs between them only in §10's own provenance
   sentence — no carrier, type or constraint changed. Results are stated over v1 as
   read at `990a822`, which is v1.
2. **`REPORT.md` could not be written.** The executing harness forbids writing
   report `.md` files; this text was returned to the orchestrator for placement at
   `prompts/2026-08-11-deference-finite-kernel/REPORT.md`. The code deliverables
   were written normally.
3. **The human-register document was not written**, for the same reason. `AGENTS.md`
   §13 requires it; §10 below names it as an outstanding action rather than leaving
   the standard silently unmet.
4. **No Lean.** The dispatch permits Lean "where natural" and forbids `lake build`.
   Shipping Lean that cannot be elaborated in this round would be exactly the
   producer's-word merge `AGENTS.md` forbids, so the port is stated as the next step
   (§10) rather than begun.
5. **T1 is stated with `D(c)` where the dispatch's target shape is
   `V_n(DELEGATE) ≥ V_n(π) − ε` with a scalar `ε`.** The scalar form is the
   `D(c) ≤ 1` corollary and is stated. The disagreement-mass form is strictly
   stronger, is what the proof gives, and is the form the certificate work needs;
   presenting only the scalar would have thrown away a derived constant.

## 8. Provisional names

New here, all provisional per `AGENTS.md` standard 6 and none proposed for
permanence: **admissible conditioning partition** (`𝒢`), **grade profile** (`G`),
**grade trust** (`GT_𝒢(η)`), **parallel-cut trust** (`GT_marg(η)`), **grade margin**
(`M(c)`), **disagreement mass** (`D(c)`), **grade regret** (`M(SIM)`),
**conformity bond** (`λ`), **transfer-bearing valuation** (`V^τ_n`).

Reused unchanged from v1 §9, not re-typed: `DELEGATE`, `FIXED`, `SIM`, `FU`,
conduct, rule, selection, quantity, well-timed, settlement instantiation, `v̂⁺`,
`P_n`, `V_n`.

## 9. Maintainer decisions surfaced

1. **Three deficiencies in skeleton v1, with minimal patches.** None applied; the
   ontology is not forked. Track C works against v1 and would have to be reconciled
   with any of these.
   - *§5.3's `τ : {(n,π)} → ℚ` cannot enforce conformity* (T5(a), W3). Minimal
     patch: `τ : {(n,π,π')} → ℚ`, read as the transfer when `π` is taken and the
     principal reports `π'`, settling at `F(n)`. Additive; no existing object
     changes type.
   - *§6's `V_n` has no slot for a transfer*, so instantiation 3 cannot act on the
     valuation at all. Minimal patch: name the variant
     `V^τ_n(c) = Σ_ω P(ω)[X_{n,c(ω)}(ω) + τ(n, c(ω), J_n(ω))]` alongside `V_n`, and
     state which is in force for a given theorem. The default `V_n` should stay the
     default.
   - *§5 types a settlement instantiation as a settled value with no notion of
     exposure to it*, so "what does this settlement yield" is not a question v1 can
     be asked. Minimal patch: §5 gains a price object `ρ_q` (`t(n)`-measurable) and
     a position `h_q`, with no-sure-gain on a `𝓕_{t(n)}`-cell as the no-exploit
     condition — the layer A3 of §5, written into the shared object so both tracks
     use the same one. This is *not* the trader machinery of §8.3 and must not be
     recorded as closing it.
2. **The settlement architecture choice remains reserved, and this round narrows
   it.** The classification says the epistemic reading is available only if
   `GT_𝒢(η)` is imported as a competence hypothesis about the principal, and that
   the enforcement reading is available unconditionally at bond `2B`. Which the
   program endorses is not a mathematical question and was not answered here.
3. **Registration.** `CLAIMS.md` does not exist. Registering the five certificates
   requires creating it; that is a specification-layer act.
4. **`FU[g]` stays a hole, and T1″ prices it.** Covering it costs
   `GT_{𝓕_{F(n)}}(η)`. Whether the program wants a theorem at that hypothesis
   strength is a maintainer call, not a track's.

## 10. Next recommended theorem or experiment

**Port T1 to Lean, with `GT_𝒢(η)` as a named hypothesis and E1's box as the
inhabitation witness.** It is the shortest path from proposal to `lean-proved` for
the round's target: the statement is a `Finset.sum` inequality over a partition, the
proof is the four lines of §1.2, the comparator class is a measurability side
condition, and E1 supplies a concrete term inhabiting the full hypothesis package
rather than a stand-in. That closes item 15's "Lean gate green with a typechecking
witness" acceptance check for the bridge half.

Second, and more informative about the program: **decide whether `GT_𝒢(η)` is
reachable at all.** The negative direction is the sharper experiment — exhibit a
settlement instantiation, or prove there is none within v1 plus a bounded exposure
layer, whose no-exploit condition implies `GT_𝒢(η)` for some `η < 2B`. §1.1 argues
the answer is no for the one-shot layer A3 because the hypothesis is not about A;
proving it, or finding the layer that escapes it, would settle whether the deference
program's finite kernel is epistemic or enforced, which is the question the roadmap
reserves.

## 11. Executor-model attribution

- Prompt-author model: GPT-5.6 Sol (OpenAI), per `PROMPT.md`.
- Orchestrator model: Claude Opus 5 (Anthropic), per `PROMPT.md`.
- Executor model: **Claude Opus 5 (Anthropic)**, model id `claude-opus-5`, this
  round, 2026-08-11.
- Review status: `ci-only`. No maintainer has read this.

---

## Outstanding maintainer actions

1. **Write this text to `prompts/2026-08-11-deference-finite-kernel/REPORT.md`**, and
   write the human-register companion `FOR_HUMANS.md` (`AGENTS.md` §13). The
   executing agent was prevented from creating either file; §7(2–3) records why.
   *(Both discharged by the orchestrator, 2026-08-11; the human register is the
   orchestrator's text, not the executing agent's, and is labelled as such.)*
2. **Decide the three v1 patches in §9(1)** — accept, reject, or defer each. If any
   is accepted, the skeleton becomes `v2` and every wave-1 track that consumed v1
   (this one and Track C at minimum) is rerun or explicitly reconciled, per v1 §10.
   Track C's certificate work is stated over the unpatched `V_n`; a `V^τ_n` patch
   changes what composes with it.
3. **Decide whether to file the Lean port of T1** as a `PRIORITIES.md` item, or to
   run it under item 15. Command if run under item 15: port T1, T1′, T1″ into
   `lean/Workspace/Deference/Contrib/`, register the declaration name as the
   statement of record, and ship E1's box as the inhabitation witness.
4. **Decide whether to create `CLAIMS.md`** and register the five certificate
   parameter sets in `certificates.json` as `enumeration-verified`, each answering
   `PRIORITIES.md` item 15. `python3 -m checkers.run CLAIMS.md` must accept them;
   they pass the unmodified house checker as of this round.
5. **Record the settlement classification's status in
   `CORRIGIBILITY_PAPER_LEDGER.md`** — Movement II's "settlement classification"
   row is `open`; this round produces a classification whose components are a
   proposal (T1 and companions) and five certificates. The ledger's vocabulary has
   no row for that combination, and choosing one is a maintainer act.
