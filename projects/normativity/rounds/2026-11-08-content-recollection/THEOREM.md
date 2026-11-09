# Content recollection — statements of record and hypothesis packages

Every named object is a declaration under `lean/Workspace/Normativity/Contrib/`. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace` from `lean/`, then
`python3.12 tests/audit_axioms.py`. Each module ends with its `#print axioms` list; every
result audits to `[propext, Classical.choice, Quot.sound]`.

Throughout, a row is `Row d` (`a · x ≤ b` over `d` rational coordinates), the cube is
`[0,1]^d`, and a bundle's region is its rows' common points in the cube.

## `rows.incompatibility-entailment` — `IncompatibilitySemantics.incEntails_iff_certEntails`

For every list of rows `Γ` and row `g`: `IncEntails Γ g ↔ CertEntails Γ g`.
`Incompatible L` is a `FarkasCert` whose rows are in `L` or are cube rows; `IncEntails Γ g` is
`∀ X, Incompatible (g :: X) → Incompatible (Γ ++ X)`; `CertEntails Γ g` is an `EntailCert` —
nonnegative multipliers on rows allowed against `Γ` whose weighted coefficients are `g.a` and
whose weighted constants sum to at most `g.b`.

*Hypotheses:* none. *Both sides occur:* true for the bound of `Conservativity.bad_forces_lower`
(through `lowerBound_certified`), false in `form_role_needs_rows`. *Rests on:*
`incompatible_iff_not_feasible`, `certEntails_iff_sem`, `incEntails_iff_sem`, and through them
`RowAlternative.alternative` and `entails_iff` (the pinned `EconCSLib` results).

## `seed.bound-certified` — `IncompatibilitySemantics.lowerBound_certified`

For a seed `S`, warrants `W`, docket `st`, settlement `F`, coordinate `φ` and rational `c`: if
`LowerBound S W st F φ c` then there are `m` and `cert : BoundCert d m φ (-1)` with every
`cert.row i` allowed against `forcedBundle S W st F` and `c ≤ -cert.value`. The upper-bound
form is `upperBound_certified`.

*Hypothesis:* the bound is valid. *Inhabited by:* `lowerBound_witness`
(`SeedStatics.defeat_widens`, the bound `1/2` on `widenSeed`). *Not assumed:* that the region
is nonempty; against an empty region every bound is certified.

## `seed.forced-interval-rational` — `IncompatibilitySemantics.forcedInterval_isForcedInterval`

If the real forced region is nonempty, `IsForcedInterval S W st F φ lo hi` holds with
`(lo, hi) = forcedInterval S W st F φ`: both are valid bounds at rational points and both are
attained at rational points of the forced region.

*Hypothesis:* `∃ x, forcedRegionR S W st F x`. *Inhabited by:* `forcedInterval_witness`
(`widenSeed`, the point `1/2`). *Rests on:* `SeedStatics.forcedInterval_spec` and
`exists_rat_point_at`, through `RowAlternative.exists_rat_of_real`.

## `expresses.kept-row-demands-no-more` — `ExpressesByRole.settled_demandsNoMore`

For an interpretation `ι : Fin d → Finset W`, a requirement `w` (events `A`, `Y`, strength
`c`, undefeated extensions `U`), coordinates `XA`, `XAY` and a rational `c'`: if `c' ≤ w.c`,
`ι XA = w.A`, `ι XAY = w.A ∩ w.Y`, and every settlement at which `settleOutcome` keeps
`strength XA XAY c'` records an event in `w.U`, then
`DemandsNoMore ι w (settled (strength XA XAY c'))`.

*Inhabited by:* `settled_expresses` (the eight-world fragment, `c' = w.c = 3/5`,
`U = keptExtensions`), consumed by `entitlementW`. *Necessity of `c' ≤ w.c`:*
`stronger_not_expresses`. *Necessity of the condition on `U`:* `defeater_not_expressed`.
*Typed, not derived:* `ι`, `w.U`.

## `expresses.entitlement-discriminates` — `ExpressesByRole.entitlement_discriminates`

Over `stateW` — two obligations exposed, admitted by the allocation `J₀`, both accounts live,
anchored at the requirement at `3/5` over the kept extensions and at the requirement at `3/4`
with the contrary challenge a defeater — an `Entitlement` exists for the row at `3/5` under
`ExpressesNoMore ι settled`, none exists for it under `ExpressesNoMore ι plain`, and none exists
for the row at `3/4` under `ExpressesNoMore ι settled`.

*Hypotheses:* none; a closed statement about the fixture. *Typed:* `ι`, the two anchors, the
contribution rule.

## `expresses.plain-row-demands-more` — `ExpressesByRole.plain_demandsMore`

If `0 < c`, `μ` is a model of `w`, the settlement `F` pins `XAY` false, the record of `F` has
positive mass and `ι XA` has positive mass on it, then
`¬ DemandsNoMore ι w (plain (strength XA XAY c))`.

*Inhabited by:* `plain_not_expresses` (the eight-world measure, the record settling `A∧Y`
false: record mass `5/8`, antecedent mass `1/8`); the conflict there is `contraCert`
(`contraposition_as_expression`).

## `content.conservative-iff-image` — `Conservativity.conservative_iff`

For a translation `T : Translation d d'` and bundles `B` over `d`, `B'` over `d'`:
`Conservative T B.Region B'.Region ↔ ∀ x, image T B'.Region x ↔ B.Region x`.

*Hypotheses:* none. *Both sides occur:* `ext₁_conservative`, `bad_not_conservative`. *Rests
on:* `refines_iff`, `addsNothing_iff`, `separating_row`, and through the last
`RowAlternative.alternative_family`.

## `precedent.consistent-iff-pairwise` — `PrecedentConstraint.consistent_iff_pairwise`

For a list of cases `Γ`: `Consistent Γ` iff for all `c, c' ∈ Γ` it is not the case that
`c.losers` covers `c'.winners` and `c'.losers` covers `c.winners`.

*Hypotheses:* none. *Both sides occur:* `precedent_consistent`, `forbidden_not_permitted`.
*Typed:* the reading of a record as a case (`caseOf`).
