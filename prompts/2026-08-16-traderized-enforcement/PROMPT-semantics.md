# Semantic repair dispatch — support-based live worlds

Continue work on PR #38. A **narrow semantic repair and theorem-reconciliation
pass**. Do not reopen the traderized-force mechanism generally: the force
results, the corrected liability bound, and the exactness regressions are
presumptively stable unless this pass directly breaks them.

## The bug

The reconciliation pass defined `Omega_t^live = S_t ∩ {0,1}^Phi`, the worlds
whose **Dirac price vector itself belongs to the admissible region**. That is not
the intended notion. The intended semantics is support-based: with `Omega_t` the
finite world set, `Delta(Omega_t)` the credal simplex, `pi_t` the map sending a
credence to its priced marginal, and `C_t = { mu : pi_t(mu) in K_t }` the
compatible credal set,

    Omega_t^live = { omega : exists mu in C_t with mu(omega) > 0 }.

A world does not have to be individually admissible as a point mass. Add the
smallest regression before changing prose: for `K = {p(A) = 1/2}` the vertex
reading returns no live worlds, while the support reading returns both.

Then recompute the laundering witness `K = {p(A) <= 1/2}`, where `p(A) = 1/2` is
compatible and gives `A = true` positive mass, so the world remains live. Answer
what the support-live worlds are, the trader's value at each, whether liability is
automatically zero, and precisely where the old proof failed — the likely error
being that `E_mu[E_t] >= 0` for every admissible `mu` does not imply
`E_t(omega) >= 0` for worlds in the support of such a `mu`.

## What to rebuild

Do not treat a price polytope and a world set as the same type. Introduce the
world space, credal simplex, pricing map, ambient constraint, compatible credal
set and support-live worlds explicitly, and do not blur price vectors, credences,
worlds, Dirac credences and supports.

Recheck deductive recovery under support semantics with both directions, and find
which formulation of the deductive region makes the reverse direction immediate.

Reopen the role of Coverage. The interesting problem is now that an admissible
credence can have nonnegative expected value while assigning tiny probability to a
live world carrying a large negative payoff. Investigate a quantitative support
condition, derive the sharp finite-dimensional inequality, and identify exactly
which additional quantity is needed — Coverage alone may not suffice unless
positive upside is also controlled, and a worldwise upper bound must be named
rather than smuggled. Use the enforcement trader's row structure.

Separate three coverage questions and do not collapse them: support existence,
which is definitional; quantitative support coverage; and diachronic legitimacy of
world removal, which may belong to provenance, answerability, settlement or
legitimacy rather than to the algebraic safety theorem.

Check nestedness: prove `C_{t+1} subseteq C_t implies Omega_{t+1}^live subseteq
Omega_t^live`, and identify which source conditions guarantee credal nesting.

Keep the generalized LIC theorem separate from Coverage; do not force
`Coverage + Liability iff LIC` unless the mathematics earns it. Preserve both
previous corrections: the withdrawn intensity-free ceiling stays withdrawn, and
the exactness case distinctions stay.

Required exact tests: the midpoint constraint; the `<= 1/2` witness; a constraint
that genuinely removes a world; deductive recovery; a credence with tiny positive
mass coexisting with a large negative worldwise payoff; a quantitative bound
limiting it; and a case where support disappears entirely.

Rewrite the "Coverage hole" verdict with the strongest true statement, rebuild the
paper theorem spine with per-step statuses and correctly computed counts, give a
fresh editorial verdict on the central paper result, and update the PR
description. Do not register speculative claims, canonize `Coverage`, identify it
with `coverage(Due)`, delete the historical record of the withdrawn vertex-based
interpretation, or claim the generalized paper is complete while quantitative
Coverage is open.

Success criterion: `admissible expectation != worldwise payoff` must be
mathematically explicit, the live-world definition must be the support one, and
seven questions must be answerable — the generalized semantic state, how live
worlds derive from it, why deduction recovers `PC(D_t)`, what the enforcement
trader guarantees, what bounded liability guarantees, what quantitative condition
lets admissible credal guarantees control worldwise live-world losses, and what
separate condition governs deleting a world from support altogether. If the sixth
or seventh remains open, say so exactly, and do not solve it by reverting to
Dirac-admissibility.
