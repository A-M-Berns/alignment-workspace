# Final formalization status

## 1. Final verdict

**CLOSED.**

No implementation artifact remains on the headline path, and the deductive specialization
is closed from the pinned source's own assumptions.

```lean
theorem DeductiveEffective.deductive_end_to_end
    (coords : ℕ → List Sentence) (nodup : ∀ n, (coords n).Nodup)
    (tol : ℕ → ℚ) (tol_pos : ∀ n, 0 < tol n)
    (hcoords : Primrec coords) (htol : Primrec tol)
    {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (hsat : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    IsLogicalInductor
        ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP) DP ∧
      ∀ n, dist2 ((deductiveProjectionSchedule coords nodup tol tol_pos).fragment n).toFinset
          ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP n)
          (fun φ => ProjectionCompiler.repEval
            ((deductiveProjectionSchedule coords nodup tol tol_pos).fragment n)
            ((deductiveProjectionSchedule coords nodup tol tol_pos).rep n (DP.D n) φ)
            ((deductiveProjectionSchedule coords nodup tol tol_pos).market DP n))
        ≤ ((tol n : ℚ) : ℝ)
```

`#print axioms` → `[propext, Classical.choice, Quot.sound]`.

The generic constraint-schedule headline, `EffectiveRepresentation.end_to_end_of_constraints_effective`,
is closed alongside it and likewise takes no supplied representation.

## 2. The hypothesis audit

The question the pass turned on: `RationalConstraintSchedule.Computation` wants the day's
region as a primitive recursive function of the *date*. For a region read off the deductive
stage that is `Primrec (fun n => DP.D n)`, and `DeductiveProcessComputation` does **not**
supply it — it is a partial recursive program that merely *eventually* emits the stage, and
no fuel search converts that into a primitive recursive function of the date.

**No extra hypothesis was added, because none is necessary.** The compiler already carries
the stage table as finite data: the recurrence runs against an explicit
`D : ℕ → Finset Sentence`, instantiated at `decodedStageTable`, which is
`fun stages n => stages.getD n ∅` and so primitive recursive outright. The pinned source's
own Trading Firm reads stages exactly that way. Two interfaces of *ours* were indexing by
the date and so could not:

* `EffectiveEnforcer.trades` — now `ℕ → Finset Sentence → List (EF × Sentence) → …`
* `ProjectionSchedule.reps` — now `ℕ → Finset Sentence → List Rep`, with `Primrec₂`

Both changes are conservative: a schedule whose region does not depend on the stage ignores
the argument, and every prior theorem keeps its statement. The one place a strengthening
could have crept in was checked explicitly — `enfAggregateFromStages_eq_aggregateAt` matches
`E.trades n (D n)` against `E.trades n (DP.D n)` using exactly `hD n le_rfl`, its existing
hypothesis.

| hypothesis | classification |
| --- | --- |
| `process : DeductiveProcessComputation DP` | **the source's own**, unchanged and unstrengthened |
| `hcoords : Primrec coords`, `htol : Primrec tol` | **intended** — the paper presents both schedules effectively |
| `tol_pos` | **intended** — a zero tolerance buys nothing |
| `nodup` | **intended** — a fragment lists each priced sentence once |
| `hsat` | **intended and necessary** — an inconsistent stage admits no world, so its region is empty and there is nothing to project onto |
| — | no implementation artifact, no supplied region, no supplied representation |

`hsat` is worth stating plainly rather than burying: it is not a computability assumption
and it is not avoidable. It is the propositional satisfiability of each stage.

## 3. Dependency chain

| arrow | names | constructive | kernel-checked |
| --- | --- | --- | --- |
| stage → atoms, assignments, consistency | dependency's `sentenceListAtoms`, `atomTableFromList`, `allBoolLists`, `tableConsistent` (+ `_primrec`) | **yes** | yes |
| stage → admissible patterns | `patternsFrom`, `admissiblePatternsEff`, `admissiblePatternsEff_primrec` | **yes** | yes |
| patterns → rational polytope | `deductivePolytopeEff`, `verts_deductivePolytopeEff` | **yes** | yes |
| polytope → nearest point | `RationalPolytope.proj`, `proj_variational`, `eq_proj_of_vertexSet` | proof-only, §6 | yes |
| polytope → affine pieces | `PolyhedralProjection.Face.piece`, `gramInvQ` | **yes** | yes |
| pieces → piecewise affinity | `PolyhedralCoverage.isPiecewiseAffineOn_proj` | existence | yes |
| max–min with the family supplied | `MaxMinRepresentation.maxMin_of_family` | **yes** | yes |
| rational feasibility | `FourierMotzkin.feasible_iff`, `feasible_primrec₂` | **yes** | yes |
| feasibility → index family → `Rep` | `ProjectorGenerator.projectorRep`, `repEval_projectorRep` | **yes** | yes |
| structured → raw compiler | `EffectiveRepresentation.compileOf`, `compileOf_primrec` | **yes** | yes |
| stage → day's representation | `deductiveReps`, `deductiveReps_primrec`, `repEval_deductiveReps` | **yes** | yes |
| representation → nearest point of the deductive region | `isNearestPoint_deductiveReps` | — | yes |
| admissibility | `DeductiveRegion.payout_mem_deductiveRegion` | — | yes |
| all → source-original LIC + every-date coherence | `deductive_end_to_end` | — | yes |

**The chain does not break.**

## 4. Explicit answers

| question | answer |
| --- | --- |
| Is any `Rep` supplied? | **No.** `deductiveReps` is computed from the stage and the fragment |
| Is any representation-correctness theorem assumed? | **No.** `repEval_deductiveReps` |
| Is any projector or region supplied? | **No.** The region is enumerated from the stage |
| Is any `ComputableMarket` supplied? | **No.** `EnforcedCompiler.computableMarket` |
| Does any `Classical.choose` determine executable syntax? | **No.** `deductiveReps`, `compileOf`, `projectorRep`, `admissiblePatternsEff` are plain `def`s; Lean refuses to compile a `def` whose data uses `Classical.choice` without a `noncomputable` marker, so the build succeeding is the check |
| Is rational feasibility executable and verified? | **Yes**, both directions, uniform in the dimension |
| Is any assumption made about `DP` beyond the source's? | **No** |

## 5. `noncomputable` on the path

`RationalPolytope.proj`, `ConstraintSchedule.target`/`targetAt` and `market` remain
`noncomputable`. The first three are proof-only — no executable definition calls them, the
trader's syntax coming from `projectionStrategy` — and `market` is the semantic recursion,
exactly as the pinned source's own `liaStates` is, with its computability the separate
`ComputableMarket` certificate that is proved. `canonicalRepresentation` is retained but is
no longer on any headline path.

## 6. Upstream

`LIACompiler.lean` gained a purely additive public section — twenty exported declarations,
none of which changes an existing one. Two are aliases for erased forms
(`sentenceListAtoms`, `atomTableFromList`); the rest are computability facts re-exported,
stated in the already-public `Sentence.atoms` / `sentenceBool` / `tableConsistent` /
`supportSentenceList` vocabulary. The one new proof is `private`: it generalises
`tableConsistentFromAtomList_sort_eq` from a sorted `Finset` of atoms to an arbitrary atom
list, which is the form a caller can supply. Declared with `lemma`, per the repository's
convention that `theorem` is reserved for statements carrying a paper label.

FAF CI is green on the pinned commit and the downstream pin points at it.

## 7. Build, test, audit

```
lake build                Build completed successfully (2974 jobs)
tests/audit_axioms.py     755 results across 48 files,
                          all within [Classical.choice, Quot.sound, propext]
tests/run.py              ALL GREEN (14 projects)
checkers.workspace_state  valid
grep -r "sorry"           none in committed Lean
FAF CI                    green; PR #2 MERGEABLE / CLEAN
```

## 8. Remaining debt

**None blocking the headline.**

- **Cost.** The generator enumerates pairs of subsets over an already-exponential face list,
  and the raw determinant adds a factorial factor. **Doubly exponential in the fragment
  dimension**, stated rather than omitted. It closes the theorem; it is not a practical
  algorithm. A singly-exponential construction plainly exists — the realised upper sets are
  cells of a hyperplane arrangement — but needs arrangement-vertex enumeration not
  formalized here.

- `PolyhedralCoverage` establishes a **cover** only: not disjoint interiors, not normal
  cones, not full-dimensionality. That is what `IsPiecewiseAffineOn` needs, but a reader
  wanting "the projection's linearity regions" does not get them here.

- The enumeration is not deduplicated. Nothing depends on it — every statement about the
  list is about membership, and a polytope's carrier is the convex hull of its vertex list.

- FAF PR #2 is green and mergeable but not yet merged; the pin points at its head commit
  rather than a commit on `main`. This is the one administrative item left, and it is the
  user's call to merge.
