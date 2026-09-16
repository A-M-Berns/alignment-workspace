# Forced-region statics

Lean: `SeedStatics.lean` §§3–6.  Executable: `src/seed.py`, `src/lp.py`, `src/fm.py`.

## 1. The forced region is a bundle, and `checkCompiled` decides it

    forcedBundle S W st F : Bundle (Cite d) d
      = live substantive rows (specialized, citing their port)
        ++ live structural rows (specialized, citing their id)
        ++ live warrant rows W (specialized)
        ++ pin rows of F (citing the settled coordinate)

    forcedRegion S W st F x := (forcedBundle S W st F).Region x

`forcedRegion_iff_check`: `forcedRegion S W st F x ↔ checkCompiled (forcedBundle S W st F) x = true`
— membership is decided by the compiler's own check, unchanged.

`forcedRegion_iff` reads the region on the unspecialized rows: `x` is in it iff `x` is
in the cube, pinned by `F`, and satisfies every live original row.  This is the form
every later theorem uses; specialization is exact on the pinned slice and otherwise
invisible.

The region is stated over the *whole* fragment with settled coordinates pinned rather
than over the unsettled coordinates alone.  The two are the same object up to the
projection that forgets pinned coordinates; the pinned form needs no re-indexing and
composes with the existing bundle type.

## 2. The forced interval, computed by elimination

For dimension `m + 1` and coordinate `φ`:

    forcedInterval S W st F φ : ℚ × ℚ
      = let cs := project m (system φ (forcedBundle S W st F)) in (lo1 cs, hi1 cs)

`system` converts cube rows and bundle rows to the elimination file's `LinCon` with `φ`
moved to position `0` by the transposition `swap φ 0` (`toLinCon_sat_iff`,
`system_sat_iff`); `project m` iterates the file's `elim` down to one coordinate
(`project_sat_iff`: exactly the projection of the real solution set onto `φ`); `lo1`,
`hi1` are the largest lower and smallest upper bound of the one-dimensional system.

`forcedInterval_spec`: if the real forced region is nonempty, both endpoints are valid
bounds on `P(φ)` over it and both are attained (at real points).
`forcedInterval_bounds`: the endpoints are valid at rational points of `forcedRegion`.
No LP optimum is taken as a hypothesis; the interval is computed and its correctness
proved, on the existing elimination file.

What is *not* proved: attainment at a *rational* point.  The elimination file states
satisfaction over `ℝ`; the constructed witness is real, and the (true) fact that a
rational system feasible over `ℝ` is feasible over `ℚ` is not in the repository.  The
rational predicate `IsForcedInterval` (valid bounds + rational attainment) is stated,
with `unique` and `mono` proved from it; the computed `forcedInterval` inhabits the real
form `forcedInterval_spec`.

The fixtures compute intervals by an exact two-phase simplex (`src/lp.py`) and cross-check
the small cases against a line-for-line transcription of the Lean elimination
(`src/fm.py`; `test_simplex_agrees_with_elimination`, `sandwich.fm_I1`,
`strict_humility.closed_item_fm`).

## 3. Seed leverage (provisional name)

    leverage I U := Σ_{φ ∈ U} (1 − (hi φ − lo φ))

over a declared list `U` of coordinates — in the fixtures, the unsettled ranking
sentences.  On the moral fixture the value is `17/5` on twelve ranking coordinates.

Two limits, recorded:

- It counts **level** content only.  A structural equality `P(x) = P(y)` drops the
  region's dimension by one and leaves every interval at `[0,1]`: leverage `0`.  A
  volume or affine-dimension measure would see it; the interval sum does not.
- It is **not monotone under settlement** in the normalized or unsettled-only forms
  (settling a coordinate removes its term); it is monotone in the all-coordinates form,
  which then credits the seed with what the world settled.  The definition ships as the
  prompt asked, with the caveat, and no normalization is defended as canonical.

The word is kept distinct from `wiki/Normativity.md`'s leverage (the clearance of a
forced-interval endpoint over a threshold): that quantity is per-endpoint and
threshold-relative; this one is a sum of widths.

## 4. Feasibility, sure loss, minimal infeasible subset

`SureLoss S W st F := ¬ ∃ x, forcedRegion S W st F x`.  `sureLoss_of_cert`: a
`FarkasCert` over the forced bundle's allowed rows (the compiler's `Bundle.Allowed`:
bundle rows and cube rows) is a sure-loss certificate — `conflict_sound` unchanged.

`FarkasCert.support_sound`: the rows with **positive** multiplier are by themselves
infeasible, so a certificate names an infeasible subset.  `MinimalInfeasible rows` is
the definition (infeasible, every one-row deletion feasible); extraction is the deletion
filter in `src/lp.py::minimal_infeasible_subset`.  The population fixture exhibits a
certificate whose support has five rows and a minimal subset of four
(`FIXTURES.md` §3).

**Empirical refutation** is `Refuted S W st F F' := F.le F' ∧ feasible on F ∧ infeasible on F'`.
A definition.

## 5. Bound certificates

`BoundCert d m φ s`: nonnegative multipliers on rows whose weighted coefficient sum is
`s · e_φ`; `BoundCert.sound` gives `s · x φ ≤ value` at every point satisfying the rows.
With `s = −1` over allowed rows this is `lowerCert_bound` (`P(φ) ≥ −value`), with
`s = 1` `upperCert_bound`.  This is the deck's dual certificate `1_φ − c = h + Σ λ_E g_E`
in row form: the rows with positive multiplier are the reasons cited.  Tightness (that
the best certificate equals the interval endpoint) is LP duality and is not proved; the
fixtures obtain the certificates by solving the dual feasibility problem and verify them
exactly (`test_farkas_and_bound_certificates`).

## 6. Monotonicity under settlement, and its failure under defeat

`forcedRegion_anti`: `F.le F'` gives `forcedRegion S W st F' ⊆ forcedRegion S W st F`.
Proof: through `forcedRegion_iff`, a point pinned by `F'` is pinned by `F` and the live
rows are the same.  `IsForcedInterval.mono`: `lo ≤ lo'` and `hi' ≤ hi`;
`forcedInterval_mono`: the same for the computed endpoints (both regions nonempty).
True, by specialization of rows, as expected.

`defeat_widens`: one item `P(0) ≥ 1/2`; with the quiet docket `1/2` is a valid lower
bound, with port `0` defeated the point `0` is in the region.  The fixture
`defeat_widening` computes `[1/2, 1]` before and `[0, 1]` after.

## 7. Item 79, the five properties

| property | this round |
|---|---|
| representability of the class | the class is "finitely many rational-coefficient endorsements over a fragment", i.e. `Bundle`; the seed's three layers and the settlement all compile into it (`forcedBundle`); a requirement outside the class is any non-affine constraint on prices, e.g. `P(φ)·P(ψ) ≤ 1/4`, which no row realizes |
| soundness | the compiler's, unchanged (`compile_sound`, `conflict_sound`) |
| completeness within the class | the forced interval is computed exactly and attained (`forcedInterval_spec`), so every valid bound on a coordinate is certified by the region itself; certificate-level completeness (LP duality) is not proved |
| joint feasibility | not addressed |
| affordable enforceability | not addressed |

The class supplied is the whole affine class; item 79 asks for a *declared requirement
class* with a compiler complete for it, and what remains is the map from `Protocol.Evidence`
types to rows and the duality half of completeness.  Not closed here.
