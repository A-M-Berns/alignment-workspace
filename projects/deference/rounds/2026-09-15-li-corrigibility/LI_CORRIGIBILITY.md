# The Expectation Provability Induction instantiation

Lean: `LICorrigibility.lean` §§3–5; fixtures: `src/compile.py`, `tests/test_compile.py`.
Labels as in `THEOREM.md`.

## 1. The instantiation, hypothesis by hypothesis

`thm:expprovind` (arXiv:1609.03543 v5): *let `(A_n) ∈ BLCS` and `b ∈ ℝ`; if for all
consistent worlds `W ∈ PC(Γ)` and all `n`, `W(A_n) ≤ b`, then `E_n(A_n) ≲_n b`.*  The
paper proves it from `thm:expcoh` in two lines.  With `A_n := B_n`, `b := 0`:

| hypothesis of the theorem | supplied by | where |
|---|---|---|
| `Γ` represents computations | the base theory of the inductor (`PA` suffices) | assumed |
| `(B_n)` is `P`-generable | the pinned syntactic certificate `LUVCombinationSyntax`, constructed from the emission of the activation sentence families and the base evaluation families | **LEAN** `MediatedPair.syntaxOf`, `LUV_COMPILATION.md` §2 |
| `‖B_n‖₁ ≤ b` | `4 + |λ_n|` with uniform `L, δ_max, D` (**LEAN** `MediatedPair.boundedSequence`) | immediate |
| `W(B_n) ≤ 0` for every `W ∈ PC(Γ)` | the architecture specification in `Γ` (MS, EX, activation semantics, the stability certificate) and the finite T2 algebra | `LUV_COMPILATION.md` §3; **LEAN** `ValidAt.value_le_of_valuesAt` |
| conclusion `E_n(B_n) ≲_n 0` | **PAPER**; **LEAN** `li_constraint_le` through the pinned `thm:expcoh` | — |
| linearity of `E_n` on a combination | the definition of `E_n` on LUV-combinations (`def:e` applied "analogously") | **LEAN** `MediatedPair.expect_eq` |

Two Lean endpoints.  `li_bypass_le` (first pass) takes the pinned library's
operational premises as named hypotheses.  `li_bypass_le_compiled` (landing pass)
constructs them: from the emission of the activation sentence families and the base
evaluation families it builds the syntactic certificate, the bounded sequence, and the
`WorldValued` premise, and concludes through `expcoh_ofSyntax`'s chain
`limsup E_n(B_n) ≤ limsup completedHigh ≤ 0`.  Its hypotheses are the realization's
inputs; `Witness.li_instance` discharges all but the deductive process's stage
consistency on a constant two-atom family.  Nothing about the market is assumed beyond
`IsLogicalInductor`.

## 2. What is imported from Logical Induction, exactly

- `def:luv`, `def:e`: the objects and the expectation operator.
- `def:tf`, `def:ece`, `def:blcp`: the admissible class.  Coefficients may depend on the
  price history only through continuous expressible features of rank `≤ n`; the LUVs
  themselves are chosen by `n`, not by prices.
- `thm:expprovind` (via `thm:expcoh`): the learning statement.  Its `W`-quantifier is
  over `PC(Γ)`, the worlds consistent with the whole theory, with no reference to what
  `D̄_n` has proved.
- `thm:wubexp` (T4 only): unbiasedness from feedback on determined combinations.

What is **not** imported and not needed: calibration of prices to any external measure;
convergence of `E_n(U_q)` to a "true" value; `thm:loe` beyond the definitional
linearity of `E_n` on combinations; any self-trust or reflective theorem.

## 3. The finite-menu argument

**Bounded menus.**  If `|Q_n| ≤ K`, arrange the menu as `K` e.c. slot sequences; each
slot's constraint satisfies T3; a finite maximum of `≲_n 0` sequences is `≲_n 0`
(**LEAN** `max_asympLE`).  No selector, no market dependence.

**Growing menus.**  The prompt's selector `q*_n := argmax_q s_q` with
`s_q := E_n(U_q) − E_n(U_𝔠q) − λ E_n(G_δ,q) − E_n(G_ρ,q) − E_n(G_M,q)` is a
discontinuous function of the day-`n` prices, hence not an expressible feature, hence
inadmissible as a coefficient (**FIX** `test_hard_argmax_is_discontinuous`: two price
vectors at sup-distance `10⁻⁶` select different pairs).  The admissible form is the
**near-argmax weighting**
```
ŵ_q  :=  ramp_{τ_n}(s_q > m_n − 2τ_n) / Σ_q' ramp_{τ_n}(s_q' > m_n − 2τ_n),
m_n := max_q s_q,     ramp_δ(x > y) := min(1, max(0, (x − y)/δ)),
```
with `τ_n → 0` an e.c. rational sequence (`τ`, not `δ`: `δ` is the mediation discrepancy).  Then:

1. `ŵ_q ≥ 0`, `Σ_q ŵ_q = 1`, and `ŵ_q > 0 ⇒ s_q > m_n − 2τ_n` (**LEAN**
   `softWeight_aggregate_ge`); the argmax's ramp is `1`, so the normaliser is `≥ 1` and the
   safe reciprocal is exact.
2. `B'_n := Σ_q ŵ_q B_q` has `‖B'_n‖₁ ≤ 4 + |λ|` and `W(B'_n) = Σ_q ŵ_q W(B_q) ≤ 0` in every
   consistent world, because validity is pairwise and the weights are nonnegative
   (**FIX** `test_convex_combination_valid_in_every_world`).  The coefficients are
   evaluated at the realized market, which is what `def:ece` and `thm:expprovind` read.
3. `E_n(B'_n) = Σ_q ŵ_q s_q ≥ m_n − 2τ_n` (**LEAN** `nearMax_weighted_ge`).
4. `thm:expprovind` on `(B'_n)` gives `E_n(B'_n) ≲_n 0`, hence `m_n ≲_n 0` (**LEAN**
   `uniform_of_soft`).

So `max_{q ∈ Q_n} s_q ≲_n 0`: the market assigns no pair of the menu an unexplained
bypass advantage, uniformly, for any **polynomial-size efficiently generated** menu:
`|Q_n| ≤ poly(n)` and the pair data emitted in polynomial time.  Ties are handled
without a rule (all near-maximal pairs share the weight).  Nothing is claimed about all
efficiently enumerable continuations: an enumerable menu is covered only on a
polynomial-size generated prefix, and a menu of superpolynomial size breaks
`P`-generability, since the weights read superpolynomially many prices.  The pinned-
interface certificate for `(B'_n)` is not constructed (`LUV_COMPILATION.md` §4).

**No reflective pathology.**  Prices enter only through continuous coefficients, which
is exactly the continuity `def:tf` imposes to make the market's fixed point exist; no
sentence names the selection; validity is checked pair by pair on the realized weights.
A hard selector would break the admissible class before it could create a paradox.

## 4. What Logical Induction contributes

- **Timeliness under bounded reasoning.**  The inequality is respected asymptotically
  by an inductor that has computed none of the trajectories, none of the evaluator's
  outputs, and has resolved no world; the instances may be arbitrarily hard for `D̄`.
  A Bayesian with a prior over `PC(Γ)` respects it trivially and computes nothing; a
  resource-bounded reasoner that checks instances respects it only after checking.
- **Uniformity over polynomial-size efficiently generated menus** (§3), which a
  reasoner checking pairs one at a time cannot have.
- **A register in which no calibration hypothesis is needed** (§5).
- **The boundary** (`FEEDBACK_BOUNDARY.md`): which quantities the inductor can be held
  to by settlement and which only by logic.

What it does not contribute: any rate (`≲_n` has none); any knowledge that
`E_n(G_δ,n)`, `E_n(G_ρ,n)`, `E_n(G_M,n)` are small; correctness of expectations on
non-settling quantities.

## 5. What remains of calibration

The 2026-09-09 T4 carried `ε_n(π)` — prices within `ε` of the securities' expectations
under an external credence.  T3 has no such term: the inequality is between the
inductor's own day-`n` expectations, and it holds for the inductor's expectations
whatever they are.  Calibration re-enters only if one wants `E_n(G_δ,n)` to be the
*physical* discrepancy; for a `Γ`-determined `G_δ,n` with an e.c. value sequence
`d_n`, `thm:expprovind` on `G_δ,n − d_n` gives `E_n(G_δ,n) ≈_n d_n`; for a settling
`G_δ,n` whose value is not e.c., T4's feedback theorem gives weighted unbiasedness; for
a same-branch `G_δ,n`, which never settles, nothing does.

## 6. The alignment reading, at the strength proved

> An agent need not be given a primitive utility bonus for human control.  If every
> protected effect has a faithful principal-mediated counterpart that keeps the
> behaviour as the principal's approve branch up to an explicit discrepancy, and the
> architecture's specification makes the resulting security inequality valid in every
> world of the inductor's theory, then the inductor learns — in a timely manner,
> uniformly over every polynomial-size efficiently generated menu of continuations, by
> its own expectations, with no calibration hypothesis — that unilateral bypass has no
> advantage over principal-mediated execution beyond the mediation discrepancy, the
> principal's decline regret, and the candidate's causal leverage over whether the
> comparison is evaluated.

This is a theorem about protected response authority, structural mediation, bounded
logical reasoning and comparison securities.  It is not a theorem about
non-manipulation or authorship (`Corrigible ∧ ¬Authored` is inhabited and the pair
satisfies the inequality with `B = 0`), about undeclared channels (`𝔠π_F = π_F`,
`B = 0`, silent), about a latent utility maximizer (the chooser scores by `E_n(U_q)`),
about all of `Π(h)` (only a polynomial-size generated menu), or about the size of the
right-hand side.  The stronger target — vanishing incentive to bypass an
*authentically reason-responsive* principal — needs the authorship and non-capture
layer as hypotheses on the evaluator, which this round does not consume.
