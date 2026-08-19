# Prompt — polyhedral coverage (verbatim as sent)

Close the last gap in a Lean 4 formalization: that the Euclidean projection onto a rational V-polytope is **piecewise affine**, i.e. that the finitely many rational affine candidate maps already built actually *cover* every point.

Repository: `A-M-Berns/alignment-workspace`.

# Setup — read carefully, it removes the two failure modes that killed earlier agents

**Branch from `origin/projection-enforcement`, NOT `origin/main`.**
```
git fetch origin projection-enforcement
git checkout -b claude/polyhedral-coverage origin/projection-enforcement
```
This matters: that branch pins `agentFoundations` at `d89817bc15d23c663d0520e3a854d6d02374074d`, and the seeded symlink points at exactly that revision's cache. If you branch from `main` (which pins the older `1fffea44`), `lake` will "reconcile" by checking out the old revision *inside another session's cache directory* and destroy it. That has already happened once.

**Seed the build state in the background and poll** — it is a multi-minute copy with no output, and the watchdog kills you after 600 s of stream silence:
```
cd <your-worktree>/lean
mkdir -p .lake
cp -RP /Users/anson/Projects/alignment-workspace/.claude/worktrees/pr40-projection/lean/.lake/packages .lake/packages
nohup cp -Rc /Users/anson/Projects/alignment-workspace/.claude/worktrees/pr40-projection/lean/.lake/build .lake/build > /tmp/seed-$$.log 2>&1 &
```
then poll every ~30 s with `du -sh .lake/build`, printing the size, until it stops growing (~400 MB). Verify `readlink .lake/packages/agentFoundations` prints the `d89817bc…` path before building. **Never run `lake update`**; never edit `lean/lakefile.toml` or `lean/lake-manifest.json`.

**Write only to a new file** `lean/Workspace/Normativity/Contrib/PolyhedralCoverage.lean`. I am concurrently editing other files on the same branch; do not modify `RationalPolytope.lean`, `PolyhedralProjection.lean`, or anything named `Projection*.lean` / `Enforced*.lean`. Your file imports what it needs.

# What already exists (read these first)

`lean/Workspace/Normativity/Contrib/RationalPolytope.lean`:
- `RationalPolytope d` with `verts : List (Fin d → ℚ)`, `verts_ne`
- `vertexSet`, `carrier = convexHull ℝ vertexSet`, `vertexSet_finite`, `carrier_convex`, `carrier_isCompact`
- `proj` (noncomputable), `proj_mem`, `proj_variational`
- `eq_proj_of_vertexSet` — **a point of the region satisfying the vertex inequalities IS the projection**
- `Pt d := EuclideanSpace ℝ (Fin d)`, `toPt : (Fin d → ℚ) → Pt d`

`lean/Workspace/Normativity/Contrib/PolyhedralProjection.lean`:
- `AffineForm d` (rational `coeff`, `const`), `AffineForm.eval`, `continuous_eval`
- `Face d` with `base : Fin d → ℚ`, `rest : List (Fin d → ℚ)`; `dim = rest.length`, `dirQ`, `dir`, `gramQ`
- `Face.Regular := IsUnit F.gramQ.det`, decidable; `regular_of_linearIndependent : LinearIndependent ℝ F.dir → F.Regular`
- `Face.piece i : AffineForm d`, `Face.candidate p : Pt d`, `candidate_apply_eq`, `continuous_candidate`
- **`Face.candidate_unique (h : F.Regular) (p x) (c : Fin F.dim → ℝ) (hx : ∀ i, x i = (F.base i : ℝ) + ∑ j, (F.dirQ j i : ℝ) * c j) (horth : ∀ l, ⟪F.dir l, p - x⟫ = 0) : x = F.candidate p`**
- `cell K F := {p | F.candidate p ∈ K.carrier ∧ ∀ v ∈ K.vertexSet, ⟪p - F.candidate p, v - F.candidate p⟫ ≤ 0}`
- `candidate_eq_proj_of_mem_cell`, `isClosed_cell`
- **`inner_eq_zero_of_active (K) (p) {w} (hw : ∀ v ∈ K.vertexSet, 0 ≤ w v) (hsum : ∑ v ∈ K.vertexSet_finite.toFinset, w v = 1) (hq : ∑ v ∈ K.vertexSet_finite.toFinset, w v • v = K.proj p) {y z} (hy hz : … ∈ …toFinset) (hwy : 0 < w y) (hwz : 0 < w z) : ⟪p - K.proj p, y - z⟫ = 0`**

Also available: PR #42's `MaxMinRepresentation.lean` (fetch `origin/claude/maxmin-representation` and cherry-pick/merge it if you want the final corollary), giving `IsPiecewiseAffineOn` and `exists_maxMin_representation`.

# The theorem to prove

```lean
theorem exists_face_mem_cell (K : RationalPolytope d) (p : Pt d) :
    ∃ F : Face d, F.base ∈ K.verts ∧ (∀ v ∈ F.rest, v ∈ K.verts) ∧ p ∈ cell K F
```

and, from it, the payoff:

```lean
theorem isPiecewiseAffineOn_proj (K : RationalPolytope d) (i : Fin d) :
    IsPiecewiseAffineOn Set.univ (fun p => K.proj p i) (…rational affine components…)
```

where the components are the `Face.piece i` of the finitely many faces built from `K.verts` (base a vertex, `rest` a sublist), viewed as `Pt d →ᵃ[ℝ] ℝ`. You will need `AffineForm.toAffineMap`. The cells are `cell K F`, which are already known closed.

If PR #42 is merged into your branch, also give the corollary via `exists_maxMin_representation`. If integrating #42 is awkward, stop at `isPiecewiseAffineOn_proj` and say so — I can do the last step.

# The proof strategy (worked out; deviate only with reason)

Let `q = K.proj p`.

1. `q ∈ carrier = convexHull ℝ vertexSet`. Apply `Set.Finite.convexHull_eq` (`K.vertexSet_finite`) to get weights `w : Pt d → ℝ` with `∀ v ∈ vertexSet, 0 ≤ w v`, `∑ v ∈ toFinset, w v = 1`, and `centerMass w id = q`. Convert the centre of mass to `∑ v ∈ toFinset, w v • v = q` with `Finset.centerMass_eq_of_sum_1`.
2. The **active** vertices are those with `0 < w v`. The active set is nonempty because the weights sum to `1`.
3. Pick any active `base₀`, and let `A` be the active vertices. By `inner_eq_zero_of_active`, `⟪p − q, y − z⟫ = 0` for **all** active `y, z`; in particular `⟪p − q, v − base₀⟫ = 0` for every active `v`.
4. `q − base₀ = ∑_{v active} w v • (v − base₀)`, because the weights sum to `1`. So `q − base₀` lies in the span of the active directions.
5. Now **thin the active set down to a linearly independent subfamily** keeping the same span. This is the only fiddly step. The recommended route avoids `Set`/`Submodule`/subtype conversions entirely: prove, by strong induction on list length, a lemma of roughly this shape —
   ```lean
   private lemma exists_regular_of_spanning (base : Fin d → ℚ) (p q : Pt d) :
       ∀ L : List (Fin d → ℚ), L.Nodup →
         (∀ v ∈ L, ⟪toPt v - toPt base, p - q⟫ = 0) →
         (∃ c : (Fin d → ℚ) → ℝ, ∀ i, q i = (base i : ℝ)
             + ∑ v ∈ L.toFinset, ((v i - base i : ℚ) : ℝ) * c v) →
         ∃ F : Face d, F.base = base ∧ (∀ v ∈ F.rest, v ∈ L) ∧ F.Regular ∧ q = F.candidate p
   ```
   **Index the coefficients by the vertex, not by `Fin L.length`.** That is the trick: dropping an element from `L` then leaves the coefficient function untouched, so no re-indexing is ever needed. In the step, if `Face.dir ⟨base, L⟩` is linearly independent you are done via `regular_of_linearIndependent` and `candidate_unique`; otherwise take a nontrivial dependence, pick `k` with a nonzero coefficient, rewrite that direction in terms of the others, absorb it into `c`, and recurse on `L.erase (L.get k)` (shorter, still `Nodup`).
   Converting the final vertex-indexed `c` to the `Fin F.dim → ℝ` that `candidate_unique` wants is `fun j => c (F.rest.get j)`, and the two sums agree because `F.rest` is `Nodup` (`List.sum_toFinset` is the bridge — that idiom is used elsewhere in this repository).
6. With the regular face in hand, `candidate_unique` gives `q = F.candidate p`. Then `p ∈ cell K F` is immediate: `F.candidate p = q ∈ carrier` by `proj_mem`, and the vertex inequalities are `proj_variational`.

If you find a materially shorter route (for instance via `exists_linearIndependent'`, or an entirely different thinning argument), take it — but say in your report what you did and why.

# Rules

- **No `sorry`, no new axioms, no `native_decide`, no floats.** CI enforces the axiom bound (`propext`, `Classical.choice`, `Quot.sound`).
- End the file with `#print axioms` lines for its public results.
- Read `AGENTS.md` and `CONTRIBUTING.md`; they govern. mathlib style, minimal typeclass assumptions, repository comment density (high in headers, low in proofs). Names provisional under `AGENTS.md` §6 — say so in the header. Avoid the identifier `Support`.
- Commits carry `Signed-off-by: A. M. Berns <ansonberns@gmail.com>` and `Model: Claude Opus 5 (Anthropic)`. No `Co-Authored-By`.

**Gates before reporting:** `python3 tests/run.py`, `python3 tests/audit_axioms.py`, `python3 -m checkers.workspace_state --check` (`--write-handoff` first if stale), and a build.

**Do not open a PR.** Push your branch `claude/polyhedral-coverage` and report the branch name — I will merge it into `projection-enforcement` myself.

# Use Aristotle liberally

`aristotle` is on PATH (`ARISTOTLE_API_KEY` in env): `aristotle submit --project-dir <dir> "<instructions>"`, then `aristotle list` / `show` / `download`. It has done well on this repository's problems when given a self-contained file (imports + definitions + the goal with one `sorry`) plus a short outline. Offload any leaf not closed in two genuine attempts; run several in parallel; never tight-poll. **Read every returned proof and confirm the statement is what you wanted.** Log what you submitted, what came back, what you kept.

# Machine load

Two other Lean processes may be running. `~/.claude/scripts/resource-guard.sh check` before heavy work; the guard's swap reading is a high-water mark and can false-positive for hours — if it blocks while the machine is quiet (load < 4, memory > 30% free), use a single capped `LEAN_NUM_THREADS=2 lake env lean <file>` to iterate on one file rather than a full build. Never run two builds at once.

# Report

The branch name; the exact final signatures; a lemma table with status; the Aristotle log; how long step 5 actually took and whether the vertex-indexed trick worked; and whether you got as far as the max–min corollary.

If something resists, do not weaken a statement silently and do not introduce a hypothesis that restates the missing fact. Report the exact desired declaration, the exact missing lemma, why it resists, and the smallest plausible next proof. Push hard before calling anything blocked.
