# Projection against rows

Both constructions compile a price region into one Logical Induction trading strategy,
both are added to the market maker's input rather than constraining its output, and
both give a finite-time conformance theorem. They differ in what the theorem is
*about*, and that difference is the whole argument.

## The two positions

Rows. A region presented as `K = {x ∈ [0,1]^d : ⟨c_j, x⟩ ≥ r_j, j = 1..m}` with
violations `g_j(P) = max(0, r_j − ⟨c_j, P⟩)` and intensities `β_j ≥ 0`:

```
ζ_row(P) = Σ_j β_j g_j(P) c_j
```

Projection. The same region as a set, `q(P) = proj_K(P)` the Euclidean nearest point
on the fragment, intensity `λ ≥ 0`:

```
ζ_proj(P) = λ (q(P) − P)
```

## They are the same trader on one halfspace

For `K = {x : ⟨c, x⟩ ≥ r}` the projection is `q(P) = P + g(P) c / ‖c‖²`, so

```
ζ_proj(P) = λ g(P) c / ‖c‖²  =  ζ_row(P)   with   β = λ / ‖c‖².
```

Checked in exact arithmetic:
`tests/test_projection.py::TestRowsAreTheSpecialCase::test_single_halfspace_positions_agree`.

So the row construction is not a different idea. It is the projection applied to one
constraint at a time and then summed — and summing single-constraint projections is
exactly the step that stops being a projection.

## What each one certifies

| | rows | projection |
| --- | --- | --- |
| force inequality | `Σ_j β_j g_j(P)² ≤ ⟨ζ, x − P⟩` for `x ∈ K` | `λ‖q − P‖² ≤ ⟨ζ, x − P⟩` for `x ∈ K` |
| what the tolerance bounds | `g_j(P) ≤ δ` for each row `j` | `d₂(P, K) ≤ δ` |
| intensity required | `β_j ≥ ρ/δ²` — but `g_j` scales with `‖c_j‖` | `λ ≥ ρ/δ²` |
| presentation-dependent | yes | no |
| route to a distance statement | needs duality/separation (Debt A) | none |
| gives the paper's `ℓ^∞` conclusion | only through Debt A | immediately, same `δ` |
| liability at a point `w` | `Σ_j β_j g_j(P) d_j(w)` — row deficits | `λ δ d₂(w, K)` |
| term size | `O(m)` | exponential in `d` |
| external mathematics | none | Ovchinnikov Thm 4.1(a), active-set piecewise affinity |
| trader is executable code | yes | yes |

## The presentation-dependence gap, exactly

Take `K = conv{(0,0), (1,0), (0,1)}` and `P = (1,1)`. Then `d₂(P, K)² = 1/2`, and it
does not move. Present `K` by the rows `x₁ ≥ 0`, `x₂ ≥ 0`, `−x₁ − x₂ ≥ −1` and scale
every normal and right-hand side by `1/N`. The region is unchanged and

```
max_j g_j(P) = 1/N  →  0.
```

So no presentation-independent constant `C` gives `d₂(P, K) ≤ C max_j g_j(P)`, which is
the paper's §9.1 claim, here on displayed rational data
(`test_rescaled_rows_shrink_the_violation_without_moving_the_region`).

The operational consequence is the intensity. To certify a Euclidean tolerance `δ` the
row route must pay `β ≥ ρ / (δ² ‖c‖²)` — for the `1/N` presentation, `N²` times what
the projection pays — while the projection route pays `λ ≥ ρ/δ²` for every
presentation of every region, because it never sees a presentation
(`test_projection_intensity_is_presentation_free`).

That factor is not an accounting curiosity. Intensity is what the enforcement trader's
liability at a non-admitted world is proportional to, so a bad presentation costs real
risk capital for the same conformance.

## What rows keep

* **Term size.** `O(m)` against an exponential. For a region that comes *already*
  presented by a few rows, and where a rowwise conformance statement is what is wanted,
  the row trader is the right one and this pass does not say otherwise.
* **Self-containedness.** No external theorem. The row compiler is closed in the
  kernel end to end, which the projection compiler is not.
* **Everything already proved about it.** `EnforcementStrategy`,
  `EnforcementPreservation`, `DeductiveEnforcement`, `CoherenceModulus`,
  `IntrinsicCoherence` are untouched by this pass and none of their theorems is
  weakened. `DeductiveEnforcement`'s preservation chain is generic in the added
  trader, which is why the projection route could reuse it without modification.

## Recommendation

Foreground the projection; keep rows as the worked special case, as the single-halfspace
identity above, and as the carrier of the presentation-dependence result that motivates
the projection in the first place. Nothing is deleted.
