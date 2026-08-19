# Projection enforcement

Whether presentation-dependent row enforcement can be replaced by an intrinsic
projection trader that holds `λ(proj_K(P) − P)` — and if so, what that does to the
paper *Generalizing and Strengthening Logical Induction*.

The round was allowed to kill the idea. It does not.

Verdict: The intrinsic projection trader survives falsification and takes over from the row construction as the paper's primary route — force, the elimination of the external opposition bound, the cumulative budget with per-date quantifiers and the deductive end-to-end theorem are kernel-checked; expressibility is closed against a cited representation theorem rather than an axiom; and the paper's ℓ∞ coherence conclusion follows from the Euclidean one at the same tolerance, which takes Debt A off the critical path.

## What is here

| file | what it is |
| --- | --- |
| `DECISION_MEMO.md` | the deliverable to read first: every question of the dispatch graded proved / proved-conditional-on-a-named-theorem / likely-but-unresolved / false |
| `PAPER_CLOSURE.md` | the recommended theorem chain, what strengthens, what stays conditional, the cleanest budget statement, and the verdict on `DistanceComplete` |
| `PAPER_AUDIT.md` | the rest of the paper, split into *wrong*, *under-justified*, and *improvable*, plus notation |
| `COMPARISON.md` | projection against rows, including the identity that makes rows the single-halfspace case |
| `COMPUTABILITY.md` | what has to be computable, what it costs, and why Debt B is untouched |
| `THEOREM_MAP.md` | paper statement ↔ Lean declaration, and the Python tests |
| `src/`, `tests/` | exact rational projection and twelve `Fraction`-exact regression tests |

Lean: `lean/Workspace/Normativity/Contrib/Projection{Force,Market,Compiler,Budget}.lean`.

## The four things that had to be true

1. **The force inequality needs only the variational inequality.** No separation
   theorem, no duality, no net, no presentation. `ProjectionForce.force_inequality`.

2. **The comparison point may be chosen after the price is displayed.** This was the
   dangerous circularity: `q = proj_K(P)` does not exist until `P` does, and the market
   maker's contract is stated at worlds. A strategy's value is affine in the assessment
   point and the cube is the convex hull of the `{0,1}` assignments on the traded
   support, so the contract extends from the vertices to the cube.
   `ProjectionMarket.marketMaker_day_value_le_cube`.

3. **The external opposition bound `M_n` is not needed.** `Strategy.absBound` is a
   computable syntactic majorant in the pinned source, so `ρ_n = ε_n + A_n` and
   `λ_n ≥ ρ_n/δ_n²` buys `d₂(P_n|_Φ, K) ≤ δ_n`.
   `ProjectionMarket.sqDist_le_slack_add_absBound`.

4. **The paper's `ℓ∞` conclusion follows from the Euclidean one at the same `δ`.**
   `‖x‖_∞ ≤ ‖x‖_2`, with the projected point as the witness.
   `ProjectionForce.sup_conformance_of_dist2`. This is what takes the exact
   dual-distance presentation off the critical path.

## The one thing that is not unconditional

That each coordinate of `p ↦ proj_K(p)` has a max–min representation over rational
affine forms. Ovchinnikov's Theorem 4.1(a) (2002) gives it, and its exact statement has
been read and matched to the use rather than assumed from folklore; the piecewise
affinity of the polyhedral projector is the standard active-set argument, written out
in `COMPUTABILITY.md §1`. The Lean development takes the representation as **data** and
its correctness as a **hypothesis** — not as an axiom and not as a `sorry` — and proves
everything on this side of it, including that the compiled strategy is executable code.

## Two negative results

* **Admission at the last date does not bound the budget.**
  `ProjectionBudget.late_admission_is_not_enough` exhibits one priced atom, a day-`0`
  region excluding the assessed world, a day-`1` region admitting everything, every
  other hypothesis satisfied, and cumulative value `−1/4`. So the zero-risk-capital
  theorem must carry `∀ k ≤ n`, and the paper's §8.1 statement — which reaches the same
  place through global nesting — is stronger than it needs to be.

* **Row presentations are not intrinsic, on displayed data.** Rescaling every normal by
  `1/N` leaves the region alone and drives the maximal violation to zero, so no
  presentation-independent constant turns violations into distance
  (`test_rescaled_rows_shrink_the_violation_without_moving_the_region`). The
  operational cost is a factor `N²` in the intensity, which is paid in risk capital.

## What is not deleted

Nothing from the row arc. `EnforcementStrategy`, `EnforcementPreservation`,
`DeductiveEnforcement`, `CoherenceModulus` and `IntrinsicCoherence` are untouched, and
no theorem about them is weakened. The projection route *reuses*
`DeductiveEnforcement`'s preservation chain unchanged, because that chain was already
generic in the added trader. For a single halfspace the two constructions are the same
trader.

## What this round did not do

It did not rewrite the paper. `PAPER_AUDIT.md` says what a rewrite has to fix, in
order, and flags the two items that are corrections rather than improvements: §6.4
currently borrows the market maker's contract at a non-world point without justifying
it, and §8.1 needs the per-date quantifier.
