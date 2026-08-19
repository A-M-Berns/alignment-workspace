# Max–min representation of piecewise affine functions

Verdict: Ovchinnikov's max–min theorem is kernel-checked for any nonempty convex domain, with no full-dimensionality, no continuity and no finite-dimension hypothesis, by replacing the source's hyperplane arrangement and tope-graph induction with a one-dimensional induction along the segment joining the two points — which also removes the genericity step the source states without proof.

Sergei Ovchinnikov, *Max–Min Representation of Piecewise Linear Functions*,
Beiträge zur Algebra und Geometrie **43** (2002) 297–302, Theorem 4.1(a); preprint
`arXiv:math/0009026`.

All of this round's content is
`lean/Workspace/Normativity/Contrib/MaxMinRepresentation.lean`. Names are
provisional (`AGENTS.md` §6).

## What is kernel-checked

Ambient: `E` a topological `ℝ`-vector space (`AddCommGroup`, `Module ℝ`,
`TopologicalSpace`, `IsTopologicalAddGroup`, `ContinuousSMul ℝ`), `ι` a finite
index type, components `g : ι → E →ᵃ[ℝ] ℝ`.

`IsPiecewiseAffineOn Γ f g` — finitely many closed `Q l` with `Γ ⊆ ⋃ l, Q l` and
`f = g (c l)` on `Q l ∩ Γ`.

| declaration | statement |
|---|---|
| `affine_apply_eq_slope` | `δ t = (δ 1 - δ 0) * t + δ 0` for `δ : ℝ →ᵃ[ℝ] ℝ` |
| `affine_eq_of_ne` | an affine function of one variable is determined by two distinct values |
| `affine_le_of_lt_of_le` | `ε a < δ a`, `δ t ≤ ε t`, `a < t ≤ b` ⟹ `δ b ≤ ε b` |
| `exists_forall_eq_of_isPreconnected` | finitely many closed sets cover a preconnected `J ⊆ ℝ`, `φ` agrees on each with one member of an affine family, no two members cross in `J` without being equal ⟹ one member agrees with `φ` on all of `J` |
| `exists_le_of_le_of_forall_selects` | the chain lemma: if `φ` agrees with one member of an affine family on every breakpoint-free closed subinterval, some member is `≤ φ` at the left end and `≥ φ` at the right end |
| `isPiecewiseAffineOn_of_finite` | the pieces may be indexed by any finite type |
| `continuousOn_of_isPiecewiseAffineOn` | `IsClosed Γ`, components continuous ⟹ `ContinuousOn f Γ` |
| `exists_le_and_le` | **Lemma 4.1**: `Convex ℝ Γ`, `x y ∈ Γ` ⟹ `∃ i, g i x ≤ f x ∧ f y ≤ g i y` |
| `exists_maxMin_representation` | **Theorem 4.1(a)**: `∃ m (S : Fin (m+1) → Finset ι) (hS : ∀ j, (S j).Nonempty), ∀ x ∈ Γ, f x = ⨆ j, ⨅ i ∈ S j, g i x` (as `Finset.sup'`/`Finset.inf'`) |
| `isPiecewiseAffineOn_maxMin` | **Theorem 4.1(b)**: a max of mins of continuous affine functions is piecewise affine on any domain (proved by Aristotle; reviewed and rebuilt here) |
| `abs_isPiecewiseAffineOn`, `maxMin_hypotheses_nonvacuous` | inhabitation witness: `|·|` on `ℝ` with components `x`, `-x` and pieces `Ici 0`, `Iic 0` |
| `segment_hypotheses` | errata witness: `[0,1] × {0} ⊂ ℝ²` is closed, convex, nonempty, has empty interior, and carries a piecewise affine function with two distinct components — so the source's arrangement `H` is empty there |

Hypotheses of the main theorem: `Convex ℝ Γ`, `Γ.Nonempty`,
`IsPiecewiseAffineOn Γ f g`, `Finite ι`. Nothing else.

Re-verify: `cd lean && lake build`, then `python3 tests/audit_axioms.py`. Each
declaration's `#print axioms` line is at the foot of the file; all fifteen audit to
`[propext, Classical.choice, Quot.sound]`.

## How the proof differs from the source

The source proves Lemma 4.1 by induction along a chain of pairwise adjacent
regions of the arrangement `{gᵢ = gⱼ}`, and finishes by density of the union of
the regions. Both steps are replaced here.

For `x, y ∈ Γ` the segment `[x, y]` lies in `Γ`, and the restrictions
`hᵢ := gᵢ ∘ lineMap x y` are affine functions of one real variable. Two of them
either coincide on the whole line or agree at a single parameter, so there are
finitely many *breakpoints* in `[0,1]`. On a breakpoint-free subinterval the
closed pieces, grouped by which restriction they carry, are relatively closed and
pairwise disjoint-or-equal, so preconnectedness forces one restriction to carry
the whole subinterval (`exists_forall_eq_of_isPreconnected`); the closed endpoints
are reached through `closure_iUnion_of_finite`, with no appeal to continuity of
`f`. Induction on the number of breakpoints then gives Lemma 4.1
(`exists_le_of_le_of_forall_selects`): the base case is a single subinterval; the
step compares the index returned for `[t₁, 1]` with the index carried by
`[0, t₁]`, and the source's "vanishes on a hyperplane, positive on one open
halfspace, hence negative on the other" becomes `affine_le_of_lt_of_le`, one
`nlinarith` on the normal form of an affine function of one variable.

Lemma 4.1 then holds for *every* pair of points of `Γ`, not only for pairs of
full-dimensional regions, so `Sᵧ := {i : f y ≤ gᵢ y}` gives `⨅_{i ∈ Sᵧ} gᵢ ≤ f`
on `Γ` directly, with equality at `y`. The maximum is over the finitely many
distinct `Sᵧ`, and no density step, no continuity of `f` and no interior are
used.

Consequences: the sign-cell reformulation the dispatch recommends is not needed —
there are no cells in this proof — and neither is the tope-graph connectivity
whose genericity argument the source omits.

## Errata in the source

1. **`H ≠ ∅` is false as stated.** §2 asserts "A simple topological argument shows
   that `H ≠ ∅`", under the standing assumption that `f` has at least two distinct
   components. Take `Γ = [0,1] × {0} ⊂ ℝ²`, `f(x₁, 0) = |x₁ - 1/2|` with pieces
   `[0,1/2] × {0}` and `[1/2,1] × {0}` and components `g₁ = x₁ - 1/2`,
   `g₂ = 1/2 - x₁`. These are distinct, `Γ` is a closed convex set, and
   `interior Γ = ∅`, so no hyperplane meets `interior Γ` and `H = ∅`. Then `T = ∅`
   and `∪T = ∅` is not dense in `Γ`, so the final step of the Theorem 4.1(a) proof
   fails. Kernel-checked as `segment_hypotheses`, except for the reading of `H`
   itself, which is not defined in Lean: what is proved is that this domain is
   closed, convex, nonempty, has empty interior, and carries a piecewise affine
   function with two distinct components.
2. **The statement survives that defect; the proof does not.** Theorem 4.1(a) is
   true for this `Γ` — `f = g₁ ∨ g₂` there — and is proved here for every nonempty
   convex `Γ`. So the missing hypothesis is a defect of the source's *proof*, not
   of its theorem, and the dispatch's instruction to carry `(interior Γ).Nonempty`
   in the Lean statement would have weakened it needlessly.
3. **Definition 2.1's "unique" is unjustified.** The affine function agreeing with
   `f` on a piece `Q` is unique only if `Q` is not contained in a hyperplane, and
   the paper's "closed domain" is never defined. Taking the components as given
   data, as here, avoids the question.
4. **The chain construction is asserted, not proved.** §3 needs `p`, `q` chosen so
   that distinct hyperplanes of `S(P,Q)` meet `[p,q]` in distinct points; the paper
   says "we can always choose `p` and `q` in such a way", with no argument. Every
   later use of adjacency — Proposition 3.1(i) and (ii), and hence the base case
   and the induction step of Lemma 4.1 — rests on it. It is the reason the source's
   route is expensive to formalize and the reason it was abandoned here.
5. **Lemma 4.1's proof uses full-dimensionality without hypothesis.** "It is zero
   on the hyperplane `H` and positive on the full–dimensional region `P`" needs `P`
   to be full-dimensional, which follows from `interior Γ ≠ ∅` and is never
   assumed.

## What is not closed

- **Corollary 4.1** (star-like domains with polyhedral boundary) is not attempted.
- **The consumer's other external fact is untouched.** `ProjectionCompiler.lean`
  cites two classical results; this round closes only the second. That the
  Euclidean projection onto a polyhedron is a piecewise affine map of the point
  being projected (Bemporad–Morari–Dua–Pistikopoulos; Rockafellar–Wets §12.E)
  remains external, and until it is closed, PR #41's representation hypothesis is
  not discharged.
- **No bridge to `ProjectionCompiler.Rep` is provided.** Its representation is a
  nested `List` folded with `max`/`min`; this development produces
  `Finset.sup'`/`Finset.inf'` over `Finset ι`. Converting one to the other is
  routine and is not done here, and the two files are on different branches by
  design.
- **Faithfulness of `IsPiecewiseAffineOn` to Definition 2.1** is argued, not
  formalized: every Definition-2.1 function satisfies it (take the same pieces and
  their components), so the theorem proved here implies the paper's. The converse
  reading is not claimed — the definition here does not require the pieces to be
  full-dimensional, to lie inside `Γ`, or the family `g` to consist exactly of the
  distinct components. Extra components in `g` are harmless: the index the chain
  lemma returns is always one that some piece carries.
