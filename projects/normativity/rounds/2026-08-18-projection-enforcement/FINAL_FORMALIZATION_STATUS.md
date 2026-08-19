# Final formalization status

## 1. Final verdict

**NOT CLOSED.**

One implementation artifact remains on the headline path, and it is named exactly:
`ConstraintSchedule.RegionRepresentation.Effective` — the certificate that the max–min
representation of the projector is produced by an algorithm rather than merely known to
exist. Everything else the pass set out to discharge is discharged.

The gap is not mathematical. `ConstraintSchedule.exists_representation` proves a correct
representation exists for **every** schedule, kernel-checked and unconditionally. What is
missing is a uniform computable function producing one, and the reason is precise:
Ovchinnikov's index sets are cut out by `Finset.univ.filter (fun T => ∃ y ∈ Γ, up y = T)`,
an existential over an infinite domain, so `ConstraintSchedule.canonicalRepresentation` is
built by `choose` and is `noncomputable`.

## 2. Strongest paper-facing theorems today

Two, and the distinction between them is the whole story.

**Conformance, with no hypotheses at all:**

```lean
theorem ConstraintSchedule.conformance_of_constraints
    (C : RationalConstraintSchedule) (DP : DeductiveProcess) (n : ℕ) :
    dist2 (C.fragment n).toFinset (C.market C.canonicalRepresentation DP n)
        (C.target C.canonicalRepresentation DP n) ≤ ((C.tol n : ℚ) : ℝ)
```

A constraint schedule and a deductive process, and nothing else. This holds because
finite-time conformance is a *semantic* statement about the market the recursion produces;
it never asks whether the enforcer's syntax was computed or chosen.

**The criterion, which does need effectiveness:**

```lean
theorem ConstraintSchedule.end_to_end_of_constraints
    (C : RationalConstraintSchedule) (hC : C.Computation)
    (R : RegionRepresentation C) (hR : R.Effective) {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP)
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → C.regionPred n v.payout) :
    IsLogicalInductor (C.market R DP) DP ∧
      (∀ n, dist2 (C.fragment n).toFinset (C.market R DP n) (C.target R DP n)
        ≤ ((C.tol n : ℚ) : ℝ)) ∧
      ∀ n, C.regionPred n (C.target R DP n) ∧
        ∀ φ ∈ (C.fragment n).toFinset,
          |C.market R DP n φ - C.target R DP n φ| ≤ ((C.tol n : ℚ) : ℝ)
```

The conclusion is the source's `IsLogicalInductor`, not a weakened or new criterion.

## 3. Dependency chain

| arrow | names | constructive | kernel-checked | classical use |
| --- | --- | --- | --- | --- |
| deductive source data → finite rational polytope | `DeductiveRegion.admissiblePatterns`, `_sound`, `_complete`, `_ne_nil_iff`, `_mem_cube` | **yes** (`def`, brute-force search, no `native_decide`) | yes | none |
| polytope → nearest point and certificate | `RationalPolytope.proj`, `proj_variational`, `eq_proj_of_vertexSet` | `proj` is `noncomputable` — proof-only, see §6 | yes | choice in `proj`, off the executable path |
| polytope → rational affine pieces | `PolyhedralProjection.Face.piece`, `candidate`, `gramInvQ` | **yes** (`det⁻¹ • adjugate`, deliberately not `Ring.inverse`) | yes | none |
| pieces → piecewise affinity | `PolyhedralCoverage.exists_face_mem_cell`, `isPiecewiseAffineOn_proj` | existence | yes | none on the executable path |
| piecewise affinity → max–min | `MaxMinRepresentation.exists_maxMin_representation`, `PolyhedralCoverage.exists_maxMin_proj` | **no — existence only** | yes | `filter` over an infinite existential |
| max–min → compiler `Rep` | `ProjectionBridge.evalR_ofGeom`, `exists_repMap_mem` | **no — `choose`** | yes | this is the gap |
| `Rep` → EF trader | `ProjectionCompiler.projectionStrategy`, `_realizes`, `repEF_denoteRat` | **yes** (`def`) | yes | none |
| trader → effective enforcer | `ProjectionEnforcer.ProjectionSchedule.enforcer`, `ProjectionEffective.scheduleTrades_primrec` | **yes** | yes | none |
| enforcer → computable market | `EnforcedCompiler.compiler`, `.computableMarket`, `ProjectionEffective.computableMarket_of_schedule` | **yes** | yes | none |
| market → finite-time conformance | `ProjectionCalibrated.dist2_le_of_calibrated`, `ConstraintSchedule.conformance_of_constraints` | semantic | yes | none |
| admission → zero liability | `ProjectionBudget.cumValue_nonneg_of_forall_mem`, `DeductiveRegion.payout_mem_deductiveRegion` | semantic | yes | none |
| all → original LIC | `EnforcedCompiler.isLogicalInductor`, `ConstraintSchedule.end_to_end_of_constraints` | — | yes | none |

**The chain breaks in exactly one link:** max–min → `Rep`. Every arrow after it is
constructive and every arrow before it is either constructive or proof-only.

## 4. Hypotheses of the headline, classified

| hypothesis | classification |
| --- | --- |
| `C : RationalConstraintSchedule` | the input itself — regions as rational polytopes, no compiled syntax |
| `hC : C.Computation` | **intended mathematical assumption** — the schedule is effectively presented. All three fields are consumed |
| `process : DeductiveProcessComputation DP` | **intended** — the source's own computability assumption |
| `hadm` | **intended** — the constraint admits every plausible world. This is what buys zero liability and is not derivable in the generic theorem |
| `R : RegionRepresentation C` | **not a substantive hypothesis** — `exists_representation` inhabits it for every `C`. It is a parameter only because the market's *syntax* depends on which representation is used, so `market` cannot quantify over it. No correctness is assumed of it |
| `hR : R.Effective` | **implementation artifact — the only one** |

Since one implementation artifact remains, the verdict is NOT CLOSED. That is the criterion,
and it is not softened here.

## 5. Explicit answers

| question | answer |
| --- | --- |
| Is any `Rep` supplied by the caller? | **No.** `RegionRepresentation` is inhabited by `exists_representation` for every schedule; correctness is a theorem (`reps_eval`), not an assumption |
| Is any representation-correctness theorem assumed? | **No.** `hrep` was the single category-(3) hypothesis of the earlier audit and is now derived from `ProjectionBridge.exists_repMap_mem` |
| Is any projector supplied? | **No.** `C.target` is *defined* as the projection of the day's price |
| Is any `ComputableMarket` supplied? | **No.** Produced by `EnforcedCompiler.computableMarket` |
| Is any enforcer-computability premise supplied? | **No.** Derived by `ProjectionEffective.scheduleTrades_primrec` from the schedule's own computability |
| Does any `Classical.choose` determine executable syntax? | **Yes — this is the gap.** `canonicalRepresentation` is `noncomputable` and built by `choose`; `R.Effective` exists precisely to demand an algorithm instead |
| Is rational feasibility itself executable and verified? | **Not yet.** In progress; mathlib has none (its Fourier–Motzkin is `linarith` meta code, and its Farkas material is dual-cone theory, not a procedure) |

## 6. `noncomputable` on the path, and why each is admissible

- `RationalPolytope.proj` — the mathematical nearest point. Proof-only: no executable
  definition calls it. The trader's syntax comes from `projectionStrategy`, which is a `def`.
- `ConstraintSchedule.target`, `targetAt` — defined *through* `proj`; they appear only in
  statements.
- `ConstraintSchedule.market` — `noncomputable` because it is the semantic recursion
  (`marketMakerStates`), exactly as the pinned source's own `liaStates` is. Its computability
  is the separate `ComputableMarket` certificate, which is proved.
- `canonicalRepresentation` — **not admissible**, and is the gap.

Axiom cleanliness does not establish computability, so this section is checked separately
from the audit and by inspection of every `noncomputable def` in the chain.

## 7. Build, test, audit

```
lake build                    Build completed successfully (2969 jobs)
tests/audit_axioms.py         621 results across 43 files,
                              all within [Classical.choice, Quot.sound, propext]
tests/run.py                  ALL GREEN (14 projects)
checkers.workspace_state      valid
grep -r "sorry"               none in committed Lean
```

## 8. Remaining debt relevant to the paper

**Headline-blocking (one item).**

*An executable generator for the projector's max–min representation.* The route is settled
and in progress:

1. **Verified rational linear feasibility.** Fourier–Motzkin over `ℚ` with an explicit
   strictness flag. `≤` and `<` are **not** identified: the strict form is genuinely
   required, because `λ_j > 0` is what distinguishes a support from a face containing it,
   and because the complement of an upper set is a strict condition. Equalities encode as
   two non-strict constraints. Satisfaction is stated over `ℝ` with rational coefficients,
   which is what lets a rational feasibility decision certify a real witness.

2. **The system is linear after introducing barycentric weights and one scalar.** The
   certificate cells are quadratic in `x`, because `⟪x − q, v − q⟫` multiplies two affine
   functions of the unknowns; feeding them to a linear checker would be a category error.
   Introducing the weights `λ` **and** the auxiliary scalar `c := ⟪x − q, q⟫` removes the
   quadratic terms, since `−⟪x,q⟫ + ⟪q,q⟫ = −c` collapses both offending products at once
   and every `⟪v_j, v_i⟫` is a rational constant. No H-representation and no facet
   enumeration are needed.

   `c` is a free variable of the system, not a definition, so it must be *forced* rather
   than assumed. It is: summing the support's equality constraints against `λ` gives
   `⟪x − q, q⟫ = c` identically. The relaxation is therefore exact, and this is the step
   the construction turns on.

3. **The active piece drops out.** With `λ` present, the projector's own value is
   `f(x) = Σ_j λ_j (v_j)_k` — already linear. So the system needs no active-face index, and
   none of `Regular`, `gramInvQ` or `candidate_eq_proj_of_mem_cell` enters it. Faces are
   needed only to supply the affine *components* `g_i` that the max–min ranges over. The
   family is indexed by pairs (support `S`, upper set `T`), and the system is

       Σ_j λ_j = 1;  λ_j = 0 for j ∉ S;  λ_j > 0 for j ∈ S
       ⟪x, v_i⟫ − Σ_j λ_j ⟪v_j, v_i⟫ − c ≤ 0   for every vertex i
       ⟪x, v_i⟫ − Σ_j λ_j ⟪v_j, v_i⟫ − c = 0   for i ∈ S
       Σ_j λ_j (v_j)_k ≤ g_i(x)                 for i ∈ T
       g_i(x) < Σ_j λ_j (v_j)_k                 for i ∉ T

   all linear in `(x, λ, c)`.

4. **Correctness reuses what is already kernel-checked.** Feasibility of `(S,T)` yields a
   witness `x` whose `q := Σ λ_j v_j` lies in `K` and satisfies the variational inequality
   at every vertex, so `q = proj_K(x)` by `RationalPolytope.eq_proj_of_vertexSet` — the
   lemma that replaced Farkas — and then `T` is exactly the upper set at `x`. Conversely
   any `x` yields a feasible pair via a barycentric representation of `proj_K(x)`. The
   family is then fed to `MaxMinRepresentation.maxMin_of_family`, so none of Ovchinnikov's
   geometry is reproved constructively.

**Honest cost.** The enumeration ranges over pairs of subsets, and `faceList` is itself
exponential in the vertex count, so the candidate count is **doubly exponential in the
fragment dimension**. This closes the theorem and is not a practical algorithm. A
singly-exponential construction plainly exists — the realised upper sets are cells of a
hyperplane arrangement, of which there are polynomially many for fixed dimension — but it
needs arrangement-vertex enumeration and general-position arguments that are not
formalized here. No complexity claim beyond "finite and effective" is made, and the
doubly-exponential bound is stated rather than omitted.

**Not headline-blocking.**

- The deductive specialization is not yet instantiated, and its two halves are in
  different states. The **semantic** half is assembly: `DeductiveRegion` supplies the vertex
  list, `admissiblePatterns_ne_nil_iff` supplies nonemptiness from stage satisfiability, and
  `payout_mem_deductiveRegion` discharges `hadm`, so `conformance_of_constraints` and
  `criterion_of_constraints` specialize to the deductive region with no computability
  hypothesis at all. The **effective** half meets a genuine interface mismatch, recorded
  here because it is easy to miss: the pinned source's `DeductiveProcessComputation` is

      ⟨code : Nat.Partrec.Code, code_spec : ∀ n, Encodable.encode (DP.D n) ∈ code.eval n⟩

  — a partial recursive program that *eventually* emits the stage — and this does **not**
  give `Primrec (fun n => DP.D n)`, which is what `RationalConstraintSchedule.Computation`
  needs in order to carry the region into the enforcer's trade list. The source absorbs its
  own weaker assumption by fuel search (`processStagePrefixAtFuel_primrec`); the region
  cannot, because `EffectiveEnforcerComputation` asks for `Primrec₂ E.trades` in the date and
  the ordinary aggregate only, with no stage data passed in.

  The honest resolution is to state the deductive specialization with an explicit primitive
  recursive stage presentation. That is **weaker than the source paper's own hypothesis** —
  arXiv:1609.03543 requires the deductive process to be *efficiently* computable, which
  implies primitive recursive — and stronger than the pinned formalization's generalization
  of it. It should be stated, not hidden, and the paper should say which of the two it is
  assuming.
- No complexity bound is claimed. `faceList K` has `|verts| · 2^{|verts|}` entries, most with
  empty cells; vertex enumeration, face enumeration, feasibility checking and max–min
  expansion may compound. **The safe claim is that the construction is finite and effective
  and that no useful polynomial or singly-exponential bound is asserted.**
- `PolyhedralCoverage` establishes a cover only — not disjoint interiors, not normal cones,
  not full-dimensionality. `IsPiecewiseAffineOn` asks only for a finite closed cover with
  agreement on each piece, so this suffices, but a reader wanting "the projection's linearity
  regions" does not have them.
- Two round `REPORT.md` files were not written by their agents (harness restriction) and the
  provisional names of six rounds await a ruling. Both are recorded in `DECISIONS.md`.
