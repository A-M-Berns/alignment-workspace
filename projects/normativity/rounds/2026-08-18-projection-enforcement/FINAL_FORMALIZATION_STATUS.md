# Final formalization status

## 1. Final verdict

**CLOSED.**

No implementation artifact remains on the headline path. The theorem of record is

```lean
theorem EffectiveRepresentation.end_to_end_of_constraints_effective
    (C : RationalConstraintSchedule) (hC : C.Computation) {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP)
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → C.regionPred n v.payout) :
    IsLogicalInductor (C.market (effectiveRepresentation C) DP) DP ∧
      (∀ n, dist2 (C.fragment n).toFinset
          (C.market (effectiveRepresentation C) DP n)
          (C.target (effectiveRepresentation C) DP n) ≤ ((C.tol n : ℚ) : ℝ)) ∧
      ∀ n, C.regionPred n (C.target (effectiveRepresentation C) DP n) ∧
        ∀ φ ∈ (C.fragment n).toFinset,
          |C.market (effectiveRepresentation C) DP n φ
            - C.target (effectiveRepresentation C) DP n φ| ≤ ((C.tol n : ℚ) : ℝ)
```

Its inputs are a schedule of rational convex constraints, the computability of that
schedule, the computability of the deductive process, and the admissibility of the
constraint. The conclusion is the pinned source's own `IsLogicalInductor`, unweakened.

`RegionRepresentation.Effective` — the certificate this document previously named as the one
thing outstanding — is discharged by `effectiveRepresentation_effective`, available for
every schedule.

## 2. What closed it

`ConstraintSchedule.canonicalRepresentation` was `noncomputable` because
`ProjectionBridge.exists_repMap_mem` is an existence proof: Ovchinnikov's index sets are cut
out by `Finset.univ.filter (fun T => ∃ y ∈ Γ, up y = T)`, an existential over an infinite
domain that no primitive recursive function can evaluate. Four things replaced it.

1. **`MaxMinRepresentation.maxMin_of_family`** — Theorem 4.1(a) with the index family
   *supplied* rather than built by the internal filter, subject to two containment
   conditions weaker than `S j = up y` in opposite directions and therefore checkable by a
   generator.

2. **`FourierMotzkin`** — rational linear feasibility, decided and verified. `feasible_iff`
   holds in both directions; `<` and `≤` are kept distinct, because `λ_j > 0` is what
   separates a support from a face containing it and the complement of an upper set is a
   strict condition. Equalities encode as two non-strict constraints. `feasible_primrec₂`
   gives the certificate **uniform in the dimension**, which the fixed-dimension form could
   not: the compiler's ambient dimension `d + m + 1` is read off its own arguments.

3. **`ProjectorGenerator`** — `projectorFamily`, `projectorRep` and `projectorRepMap` as
   `def`s, with `repEval_projectorRepMap` matching `exists_repMap_mem`'s conclusion exactly.
   The construction turns on two points. The certificate cells are quadratic in `x`, and
   introducing the barycentric weights `λ` together with the auxiliary scalar
   `c := ⟪x − q, q⟫` removes both quadratic terms at once, since every `⟪v_j, v_i⟫` is a
   rational constant. `c` is a free variable of the system rather than a definition, so it
   had to be *forced*: `cOf_eq_of_holds` proves it is, by summing the support's residual
   equations against `λ`. With `λ` present the projector's own value `Σ_j λ_j (v_j)_k` is
   already linear, so no active-face index enters the system and none of `Regular`,
   `gramInvQ` or `candidate_eq_proj_of_mem_cell` is used by it — faces supply only the
   affine components.

4. **`EffectiveRepresentation`** — the same pipeline a second time over raw, proof-free,
   non-dependent data, with an agreement lemma at every step. This was necessary because
   `projectorRep` takes a `Fragment` (a list bundled with a `Nodup` proof) and a
   `RationalPolytope F.coords.length` (vertices in a type depending on the fragment), and
   neither is `Primcodable`. The obstruction was never that the generator is ineffective,
   but that its *type* is not one a computability statement can mention.

## 3. Dependency chain

| arrow | names | constructive | kernel-checked |
| --- | --- | --- | --- |
| deductive source data → finite rational polytope | `DeductiveRegion.admissiblePatterns`, `_sound`, `_complete`, `_ne_nil_iff`, `_mem_cube` | **yes** | yes |
| polytope → nearest point and certificate | `RationalPolytope.proj`, `proj_variational`, `eq_proj_of_vertexSet` | proof-only, see §6 | yes |
| polytope → rational affine pieces | `PolyhedralProjection.Face.piece`, `gramInvQ` | **yes** | yes |
| pieces → piecewise affinity | `PolyhedralCoverage.exists_face_mem_cell`, `isPiecewiseAffineOn_proj` | existence | yes |
| piecewise affinity → max–min, family supplied | `MaxMinRepresentation.maxMin_of_family` | **yes** | yes |
| rational feasibility | `FourierMotzkin.feasible`, `feasible_iff`, `feasible_primrec₂` | **yes** | yes |
| feasibility → index family → `Rep` | `ProjectorGenerator.projectorFamily`, `projectorRep`, `repEval_projectorRep` | **yes** | yes |
| structured `Rep` → raw compiler | `EffectiveRepresentation.compileOf`, `projectorRepOf_eq` | **yes** | yes |
| raw compiler → `Primrec₂` | `compileLen_primrec`, `compileOf_primrec` | **yes** | yes |
| compiler → `RegionRepresentation` + `Effective` | `effectiveRepresentation`, `effectiveRepresentation_effective` | **yes** | yes |
| `Rep` → EF trader | `ProjectionCompiler.projectionStrategy`, `_realizes` | **yes** | yes |
| trader → effective enforcer | `ProjectionEffective.scheduleTrades_primrec` | **yes** | yes |
| enforcer → computable market | `EnforcedCompiler.computableMarket` | **yes** | yes |
| all → original LIC | `end_to_end_of_constraints_effective` | — | yes |

**The chain no longer breaks.** Every arrow is constructive or proof-only.

## 4. Hypotheses of the headline, classified

| hypothesis | classification |
| --- | --- |
| `C : RationalConstraintSchedule` | the input itself — regions as rational polytopes, no compiled syntax |
| `hC : C.Computation` | **intended** — the schedule is effectively presented. All three fields consumed |
| `process : DeductiveProcessComputation DP` | **intended** — the source's own computability assumption |
| `hadm` | **intended** — the constraint admits every plausible world. This buys zero liability, and is the paper's normative input |
| — | no implementation artifact remains |

## 5. Explicit answers

| question | answer |
| --- | --- |
| Is any `Rep` supplied by the caller? | **No.** `effectiveRepresentation C` is constructed from `C` |
| Is any representation-correctness theorem assumed? | **No.** `reps_eval` is proved from `repEval_projectorRep` |
| Is any projector supplied? | **No.** `C.target` is *defined* as the projection of the day's price |
| Is any `ComputableMarket` supplied? | **No.** Produced by `EnforcedCompiler.computableMarket` |
| Is any enforcer-computability premise supplied? | **No.** Derived by `ProjectionEffective.scheduleTrades_primrec` |
| Does any `Classical.choose` determine executable syntax? | **No.** `effectiveRepresentation` and `compileOf` are plain `def`s. Lean refuses to compile a `def` whose data uses `Classical.choice` without a `noncomputable` marker, so the build succeeding *is* the check |
| Is rational feasibility itself executable and verified? | **Yes.** `FourierMotzkin.feasible`, with `feasible_iff` both ways and `feasible_primrec₂` |

## 6. `noncomputable` on the path

`RationalPolytope.proj`, `ConstraintSchedule.target`/`targetAt` and
`ConstraintSchedule.market` remain `noncomputable`, and all are admissible: the first three
are proof-only — no executable definition calls them, the trader's syntax coming from
`projectionStrategy` — and `market` is the semantic recursion, exactly as the pinned
source's own `liaStates` is, with its computability the separate `ComputableMarket`
certificate that is proved.

`canonicalRepresentation` is still present and still `noncomputable`. It is no longer on the
headline path, and is retained only because `conformance_of_constraints` and
`criterion_of_constraints` are stated at it.

## 7. Build, test, audit

```
lake build                    Build completed successfully (2973 jobs)
#print axioms                 all 25 declarations of EffectiveRepresentation within
                              [propext, Classical.choice, Quot.sound]
grep -c sorry                 0 in the new file; none in committed Lean
noncomputable in new file     none
```

`Classical.choice` in the axiom list is unavoidable and does not compromise computational
content: mathlib reaches `Mul ℚ` through structures with classical proof fields, so even
`def t (p q : ℚ) := p * q` reports it. `Classical.choose` appears nowhere.

## 8. Remaining debt relevant to the paper

**None blocking the headline.**

- **Cost.** The generator enumerates pairs of subsets over an already-exponential face list,
  and the raw determinant adds a factorial factor on top. **The construction is doubly
  exponential in the fragment dimension, and this is stated rather than omitted.** It closes
  the theorem; it is not a practical algorithm. A singly-exponential construction plainly
  exists — the realised upper sets are cells of a hyperplane arrangement — but needs
  arrangement-vertex enumeration not formalized here.

- **The deductive specialization's effective half.** `DeductiveSchedule` closes the semantic
  half: `regionPred_eq_deductiveRegion` identifies the constraint schedule's region with
  `DeductiveRegion.deductiveRegion`, `hadm_of_deductive` discharges admissibility, and
  conformance and criterion specialize with conclusions unchanged. Instantiating
  `end_to_end_of_constraints_effective` at a deductive schedule additionally needs
  `Primrec fun n => admissiblePatterns (DP.D n) (coords n)`, which reduces to `Primrec` for
  `Sentence.atoms`, `sentenceBool` and `tableConsistent`. The pinned dependency proves
  exactly these at `LIACompiler.lean` 5279–5560 — `atomListTable_prim`,
  `formulaBoolStep_prim`, `formulaBoolDecoded_prim`, `sentenceBoolFromAtomList_prim`,
  `tableConsistentFromAtomList_prim` — and **all five are `private`**. This is module
  visibility, not mathematics: the same blocker Debt B had, resolved then by a purely
  additive public re-export upstream (`d89817bc`), and the same remedy applies. Note also
  that `DeductiveProcessComputation` supplies a partial recursive code, not `Primrec DP.D`,
  so the deductive specialization will need an explicit primitive-recursive stage
  presentation — weaker than arXiv:1609.03543's own "efficiently computable" hypothesis,
  stronger than the pinned formalization's generalization of it, and to be stated rather
  than hidden.

- `PolyhedralCoverage` establishes a **cover** only — not disjoint interiors, not normal
  cones, not full-dimensionality. That is exactly what `IsPiecewiseAffineOn` needs, but a
  reader wanting "the projection's linearity regions" does not get them here.

- FAF PR #2 is pinned at a branch commit rather than a merged one. This is the one
  administrative irregularity.
