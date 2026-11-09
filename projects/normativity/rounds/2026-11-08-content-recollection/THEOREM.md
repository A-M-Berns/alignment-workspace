# Content recollection — statements of record and hypothesis packages

Every named object is a declaration under `lean/Workspace/Normativity/Contrib/`. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace` from `lean/`, then
`python3.12 tests/audit_axioms.py`. Each module ends with its `#print axioms` list; every
result audits to `[propext, Classical.choice, Quot.sound]`.

Throughout, a row is `Row d` (`a · x ≤ b` over `d` rational coordinates), the cube is
`[0,1]^d`, and a bundle's region is its rows' common points in the cube.

## The row logic

**Syntax.** A formula is a row `a · x ≤ b` with `a ∈ ℚ^d`, `b ∈ ℚ` (`Row d`); a theory is a
finite list of rows, or a bundle of cited rows. The cube rows `x i ≤ 1`, `−x i ≤ 0`
(`cubeRows d`) are available in every derivation (`IncompatibilitySemantics.Allowed`).

**Semantics.** A model is a rational point of the cube; `r.Sat x` is satisfaction. A list is
*feasible* when it has a model (`Feasible`); `Γ` *semantically entails* `g` when `g` holds at
every model of `Γ` (`SemEntails`); a region *forces* a row that holds at each of its points
(`Conservativity.Forces`). A rational list with a real solution has a rational one
(`RowAlternative.exists_rat_of_real`).

**Consequence.** A *refutation* of `Γ` is a `FarkasCert` over allowed rows: nonnegative
multipliers with vanishing coefficient sum and negative constant sum (`Incompatible`). A
*derivation* of `g` from `Γ` is an `EntailCert`: nonnegative multipliers on allowed rows whose
weighted coefficients are `g.a` and whose weighted constants sum to at most `g.b`
(`CertEntails`). Both are finite objects: multipliers and rows, checked by finitely many rational
equalities and inequalities.

**Soundness and completeness**, with no nonemptiness hypothesis: `Incompatible Γ ↔ ¬ Feasible Γ`
(`incompatible_iff_not_feasible`); `CertEntails Γ g ↔ SemEntails Γ g` (`certEntails_iff_sem`);
and the definition of consequence by incompatibility agrees with both
(`incEntails_iff_certEntails`). Completeness rests on the pinned `EconCSLib` alternative
(`RowAlternative.alternative`, `entails_iff`). Existence of a certificate is proved; no
procedure here searches for one.

**Translation and elimination.** A translation `T` pulls a row back to a row, valid at `y` iff
the row is valid at `T.apply y` (`Conservativity.pull_sat_iff`). Eliminating a coordinate is
computed: the rows `Forgetting.eliminate k L` hold at a rational `x` iff `x` is the restriction
of a model of `L` (`eliminate_sat_iff`), so the consequences of a theory over the remaining
coordinates are exactly the consequences of the eliminated theory (`forget_exact`,
`forget_certified`).

**Predicates defined in it.**

| predicate | declaration | reads |
|---|---|---|
| a valid bound on a coordinate, certified | `SeedStatics.BoundCert`, `lowerBound_certified` | a derivation of `s · x φ ≤ v` |
| refines, adds nothing, conservative | `Conservativity.Refines`, `AddsNothing`, `Conservative` | forced rows of two regions across `pull` |
| broken commitment | `Recollection.Broken`, `VocabularyAct.BrokenAlong` | a row forced by the old region whose pullback the new does not force |
| licence of a vocabulary change | `VocabularyAct.Licensed` | a derivation of the pullback of each protected row and old cube row |
| challenge to a vocabulary change | `VocabularyAct.Challenge`, `Challenge.Valid` | a derivation of a row from old rows, and a model of the new rows refuting its pullback |
| charge of a commitment | `VocabularyAct.Charge` | the largest excess of its pullback over the new region |
| demands no more | `ExpressesByRole.DemandsNoMore` | refutations against a content's rows at a record, and against a requirement's models |
| cited functional certificate | `WarrantForce.FunctionalCert`, `AdapterCertificates.exists_citedFunctional` | a derivation of a bound on a linear functional |

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
`U = keptExtensions`), consumed by `entitlementW`. *Sufficient, with no converse proved.* *Necessity of `c' ≤ w.c`:*
`stronger_not_expresses`. *Necessity of the condition on `U`:* `defeater_not_expressed`.
*Typed, not derived:* `ι`, `w.U`.

## `expresses.entitlement-discriminates` — `ExpressesByRole.entitlement_discriminates`

Over `stateW` — two obligations exposed, admitted by the allocation `J₀`, both accounts live,
anchored at the requirement at `3/5` over the kept extensions and at the requirement at `3/4`
with the contrary challenge a defeater — an `Entitlement` exists for the row at `3/5` under
`ExpressesNoMore ι settled`, none exists for it under `ExpressesNoMore ι plain`, and none exists
for the row at `3/4` under `ExpressesNoMore ι settled`.

*Hypotheses:* none; a closed statement about the fixture. *Typed:* `ι`, the two anchors, the
contribution rule. Exposure, admission and liveness hold for both obligations by construction;
expression is what separates the three cases.

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

## `precedent.rationalizable-iff-acyclic` — `PrecedentConstraint.rationalizable_iff_acyclic`

For a list of cases `Γ`: `Rationalizable Γ ↔ ∀ c, ¬ Relation.TransGen (Next Γ) c c`.
`Rationalizable Γ` is an irreflexive, transitive relation on reason sets containing every
case's decision (`V` beats `U` when `V` covers the case's winners and its losers cover `U`);
`Next Γ c c'` holds when both are in `Γ` and `c.losers` covers `c'.winners`.

*Hypotheses:* none. *Both sides occur:* `permitted_distinguished` (by `rationalizable_of_rank`),
`forbidden_not_permitted`, `cycle_not_rationalizable`. *Weaker than it:* the pairwise condition
`consistent_iff_pairwise`, by `cycle_not_rationalizable`. *Typed:* the reading of a record as a
case (`caseOf`).

## `precedent.permitted-iff-reach` — `PrecedentHolding.permitted_iff`

For a list of cases `Γ` and a case `c`:
`Permitted Γ c ↔ Rationalizable Γ ∧ ¬ Reach Γ c.losers c.winners`. `Holding Γ` is
`Relation.TransGen (Dominates Γ)`; `Reach Γ V U` is `Covers V U ∨ Holding Γ V U`.

*Hypotheses:* none. *Both sides occur:* `PrecedentConstraint.permitted_distinguished`,
`forbidden_not_permitted`. *Rests on:* `holding_cons` — the holding of `c :: Γ` from the holding
of `Γ` and `c`. *With it:* `permitted_append_congr` (same holding, same permissions after any
continuations); `permission_eq_iff_reach_eq` (among rationalizable bases, same permissions iff
same reach; its hypotheses inhabited by `holding_not_minimal`); `reachSet_eventually_const`
(over a finite set of reason sets). *Typed:* the reading of a record as a case.

## `precedent.staircase-irredundant` — `PrecedentHolding.staircase_irredundant`

For `s : ℕ → ℚ` strictly increasing and `i < n`: `¬ Permitted (staircase s n) (against s i)` and
`Permitted ((staircase s n).filter fun c => c ≠ step s i) (against s i)`, where `step s j` is
`⟨[premise 0 (s j)], [premise 1 (s j)]⟩`, `against s i` its reverse at `s i`, and `staircase s n`
the steps for `j < n`.

*Hypotheses:* `StrictMono s`, `i < n`. *Inhabited by:* `staircase_witness` (`humbleScale`,
`n = 3`, `i = 1`); `humbleScale_spec` puts the scale inside `(0,1)`.

## `precedent.assessor-sets-precedent` — `AssessedConduct.assessor_sets_precedent`

For every verdict `v`: `¬ Permitted [first.case] (again v).proposal` and
`Permitted [first.proposal] (again v).proposal`. `first` is the act on `P(X) ≥ 3/4` against
`P(¬X) ≥ 1/2` assessed a shortfall, so `first.case = ⟨[P(¬X) ≥ 1/2], [P(X) ≥ 3/4]⟩`; `again v`
is the act on `P(X) ≥ 7/10` against `P(¬X) ≥ 3/5`.

*Hypotheses:* none; a closed statement about the fixture. *Typed:* the reading of an act with
its grounds and the grounds against it as a proposal, and of the verdict as fixing which side
won; `ofCertificate`'s instantiation of `ActCertificate` at `Ent := Form d`.

## `content.forget-region-is-projection` — `Forgetting.forget_region`

For `k : Fin (d + 1)`, a bundle `B` over `d + 1` coordinates and `x : Fin d → ℚ`:
`(forget k B).Region x ↔ projection k.succAbove B.Region x`.

*Hypotheses:* none. *Rests on:* `FourierMotzkin.elim_sat_iff` (real points) and
`RowAlternative.exists_rat_of_real` (the rational witness), through `eliminate_sat_iff`.
*Both sides occur:* `live_forget_cost` (the projections of two forced regions).

## `content.forget-settled` — `Forgetting.forget_settled`

For a seed `S` over `d + 1` coordinates, warrants `W`, docket state `st`, settlements `F`, `F'`,
`k` with `F.val k = some b` and `F.le F'`: `projection k.succAbove (forcedRegion S W st F') x` iff
`InCube x`, `(dropSettlement k F').Pinned x`, and `(dropCoord k (specialize F r)).Sat x` for the
row `r` of every item of `S.liveSub st ++ W` and of `S.liveStr st`.

*Hypotheses:* `F.val k = some b`, `F.le F'`. *Inhabited by:* `forget_settled_witness`
(`liveSeed`, `X` settled true, `F' = F`). *Necessity of the first:* `live_forget_cost` — with
`k` unsettled the projection taken before the settlement does not give the forced region after
it.

## `content.licensed-no-challenge` — `VocabularyAct.licensed_no_challenge`

For a vocabulary change `V` with `Licensed V` and any challenge `c`:
`¬ c.Valid V V.fragment`.

*Hypothesis:* `Licensed V`. *Inhabited by:* `split_licensed` (the split change with
`P(S₁) ≥ 1/5`, `P(S₂) ≥ 1/5`, protecting the two credence rows), consumed in
`splitChallenge_valid`. *The converse:* `unlicensed_has_challenge`. *Outside the fragment:*
`splitChallenge_valid` — `P(S) ≥ 1/2` is validly challenged against the old commitments.
*Typed:* the protected fragment; the owner, which nothing reads.

## `memory.live-forget-cost` — `Forgetting.live_forget_cost`

Over `liveSeed` — coordinates `(X, Y)`, the one item `P(Y) ≥ 3/4 · P(X)`: the projection along
the map dropping `X` of the forced region under the empty settlement is the cube on `Y`;
`IsForcedInterval liveSeed [] DocketState.quiet settledX 1 (3/4) 1`; and the projection of the
forced region under `settledX` is `{x | InCube x ∧ 3/4 ≤ x 0}`.

*Hypotheses:* none; a closed statement about the fixture.

## `memory.schedule-slack` — `Forgetting.schedule_slack`

For `K K₀ : ∀ t, Recollection (n (t + 1)) (n t)` and sets `B t` of stage-`t` worlds with `K t`
and `K₀ t` agreeing off `B t`, a nonnegative `q` on the first worlds, and bounds `lo`, `hi`: for
every `T` and every row `r` over the stage-`T` worlds with coefficients in `[lo, hi]`,
`excess r ((chain K T).push q) ≤ excess r ((chain K₀ T).push q) + (hi − lo) · scheduleLoss K B q T`,
where `scheduleLoss K B q T = Σ_{t < T} Σ_{w ∈ B t} (chain K t).push q w`.

*Hypotheses:* agreement off `B t`; `q` nonnegative; the coefficient bounds. *Inhabited by:*
`schedule_slack_witness`. *With it:* `schedule_bounded`, `schedule_summable` — a bound uniform
in `T` where the stage masses are bounded by a sequence with bounded partial sums, or a
summable one. *Rests on:* `Recollection.approx_step`, `retold_bounds`, `excess_pull`.

## `memory.selective-forgetting` — `Forgetting.selective_forgetting`

Over `recOn a` — coordinates `(φ, A, B)`, the one item `P(φ) ≥ 3/4 · P(a)` — with
`afterForget a k later` the projection along the map dropping `k` of the forced region under the
empty settlement, pinned by the retained one of `A`, `B` settling true:
`IsInterval (afterForget 1 1 later) 0 0 1`, `IsInterval (afterForget 2 2 later) 0 0 1`,
`IsInterval (afterForget 2 1 later) 0 (3/4) 1`, `IsInterval (afterForget 1 2 later) 0 (3/4) 1`,
and `IsForcedInterval (recOn a) [] DocketState.quiet bothTrue 0 (3/4) 1` for `a = 1, 2`.

*Hypotheses:* none; a closed statement about the fixture. `later_eq`: `later` is `bothTrue`
restricted to the retained coordinates, whichever of `A`, `B` is dropped.

## `seed.adapter-certificates-exist` — `AdapterCertificates.exists_citedFunctional`

For a bundle `B : Bundle (Cite d) d`, a functional `ℓ` and a rational `v`: if
`∀ y, B.Region y → ∑ j, ℓ j * y j ≤ v` then there is `c : CitedFunctional d ℓ` with
`c.CitesLive B` and `c.cert.value ≤ v`.

*Hypothesis:* the bound is valid. *Inhabited by:* `citedFunctional_witness`
(`SeedStatics.widenSeed`, `−P(0) ≤ −1/2`). *With it:* `excludes_of_region`, `margins_of_region`.
*Not assumed:* that the region is nonempty.
