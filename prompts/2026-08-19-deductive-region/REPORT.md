# Report — the deductive coherence region as a rational vertex list

## Model attribution

- **Prompt-author model:** unrecorded
- **Executor model:** Claude Opus 5 (Anthropic)
- **Dates:** 2026-08-19

## What was delivered

One proof-layer file, `lean/Workspace/Normativity/Contrib/DeductiveRegion.lean`.
Twenty-one public declarations, no `sorry`, no new axioms, no `native_decide`, no
floats. Every one audits to `[propext, Classical.choice, Quot.sound]` or a subset;
`tests/audit_axioms.py` reports 465 results across 26 files, all within the bound.

The enumerator is a **computable `def`**. `#eval admissiblePatterns {p} [p, q]`
returns `[[1, 0], [1, 1]]`, and the same equation is proved by `decide +kernel`.

## Exact final signatures

```lean
namespace Workspace.Normativity.Contrib.DeductiveRegion

def admissiblePatterns (D : Finset Sentence) (coords : List Sentence) : List (List ℚ)

theorem admissiblePatterns_sound (D : Finset Sentence) (coords : List Sentence)
    {w : List ℚ} (hw : w ∈ admissiblePatterns D coords) :
    ∃ v : PCWorld, v.ConsistentWith D ∧ w = coords.map (ratPayout v)

theorem admissiblePatterns_complete (D : Finset Sentence) (coords : List Sentence)
    (v : PCWorld) (hv : v.ConsistentWith D) :
    coords.map (ratPayout v) ∈ admissiblePatterns D coords

theorem admissiblePatterns_ne_nil_iff (D : Finset Sentence) (coords : List Sentence) :
    admissiblePatterns D coords ≠ [] ↔ ∃ v : PCWorld, v.ConsistentWith D

theorem admissiblePatterns_nonempty (D : Finset Sentence) (coords : List Sentence)
    (hD : ∃ v : PCWorld, v.ConsistentWith D) : admissiblePatterns D coords ≠ []

theorem admissiblePatterns_mem_cube (D : Finset Sentence) (coords : List Sentence)
    {w : List ℚ} (hw : w ∈ admissiblePatterns D coords) {x : ℚ} (hx : x ∈ w) :
    x = 0 ∨ x = 1

theorem admissiblePatterns_length (D : Finset Sentence) (coords : List Sentence)
    {w : List ℚ} (hw : w ∈ admissiblePatterns D coords) : w.length = coords.length

def restrictTo (coords : List Sentence) (p : Sentence → ℝ) : Fin coords.length → ℝ
def vertex (coords : List Sentence) (w : List ℚ) : Fin coords.length → ℝ

def deductiveVertices (D : Finset Sentence) (coords : List Sentence) :
    Set (Fin coords.length → ℝ)

def deductiveRegion (D : Finset Sentence) (coords : List Sentence) :
    (Sentence → ℝ) → Prop

theorem payout_mem_deductiveRegion (D : Finset Sentence) (coords : List Sentence)
    (v : PCWorld) (hv : v.ConsistentWith D) : deductiveRegion D coords v.payout

theorem deductiveRegion_fragmentLocal (D : Finset Sentence) (coords : List Sentence)
    {p q : Sentence → ℝ} (h : ∀ φ ∈ coords, p φ = q φ) :
    deductiveRegion D coords p ↔ deductiveRegion D coords q

theorem deductiveRegion_subset_cube (D : Finset Sentence) (coords : List Sentence)
    {p : Sentence → ℝ} (hp : deductiveRegion D coords p) (i : Fin coords.length) :
    restrictTo coords p i ∈ Set.Icc (0 : ℝ) 1

theorem deductiveRegion_eq_convexHull (D : Finset Sentence) (coords : List Sentence)
    (hnd : coords.Nodup) :
    restrictTo coords '' {p | deductiveRegion D coords p}
      = convexHull ℝ (deductiveVertices D coords)
```

`ratPayout` is `AssessmentProcess.ratPayout : PCWorld → Sentence → ℚ`, the
dependency-side `{0,1}` payout table, with
`payout_eq_ratPayout : v.payout φ = (ratPayout v φ : ℝ)` already in the repository.

## The exact consistency hypothesis nonemptiness needs

`∃ v : PCWorld, v.ConsistentWith D` — the stage is propositionally satisfiable.
Nothing about the fragment enters, and `coords` may be empty or contain repeats.

It is shown to be exact rather than merely sufficient: `admissiblePatterns_ne_nil_iff`
proves the biconditional, so no weaker hypothesis suffices and no stronger one is
used. `admissiblePatterns_nonempty` is the one-directional corollary the dispatch
asked for.

## Lemma table

| declaration | status |
|---|---|
| `fragmentAtoms`, `regionContext`, `contextList`, `tableOf` | proved — search-space definitions, computable |
| `atoms_subset_fragmentAtoms` | proved |
| `atoms_subset_regionContext_of_mem_stage` / `_of_mem_coords` | proved |
| `mem_contextList` | proved |
| `tableOf_map` | proved |
| `admissiblePatterns` | proved — computable `def` |
| `admissiblePatterns_sound` | proved |
| `sentenceBool_tableOf_iff` | proved — the "only context atoms matter" step |
| `admissiblePatterns_complete` | proved |
| `admissiblePatterns_length` | proved |
| `ratPayout_eq_zero_or_one` | proved |
| `admissiblePatterns_mem_cube` | proved |
| `admissiblePatterns_ne_nil_iff` | proved |
| `admissiblePatterns_nonempty` | proved |
| `restrictTo`, `vertex`, `deductiveVertices`, `deductiveRegion` | proved — definitions |
| `vertex_map`, `restrictTo_payout` | proved |
| `payout_mem_deductiveRegion` | proved |
| `deductiveRegion_fragmentLocal` | proved |
| `deductiveRegion_subset_cube` | proved |
| `extend`, `restrictTo_extend` | proved — `restrictTo_extend` needs `coords.Nodup` |
| `deductiveRegion_eq_convexHull` | proved — needs `coords.Nodup` |
| `region_worked_instance` | proved by `decide +kernel` |
| `region_inconsistent_stage` | proved by `decide +kernel` |
| `region_fragment_shares_atom` | proved by `decide +kernel` |
| `region_fragment_entailment` | proved by `decide +kernel` |
| `region_independent_fragment` | proved by `decide +kernel` |
| `witnessWorld_consistent`, `witness_stage_satisfiable` | proved |
| `witness_nonempty`, `witness_payout_mem_region`, `witness_coords_nodup` | proved |

Nothing is blocked, weakened, or admitted.

## Kernel-checked instances

All by `decide +kernel`; the kernel runs the whole search.

| statement | value |
|---|---|
| `admissiblePatterns {p} [p, q]` | `[[1, 0], [1, 1]]` |
| `admissiblePatterns {p ⋏ ∼p} [p, q]` | `[]` |
| `admissiblePatterns ∅ [p, ∼p]` | `[[0, 1], [1, 0]]` |
| `admissiblePatterns ∅ [p, p ⋏ q, q]` | `[[0,0,0], [0,0,1], [1,0,0], [1,1,1]]` |
| `admissiblePatterns ∅ [p, q]` | `[[0, 0], [0, 1], [1, 0], [1, 1]]` |

The third is the case the dispatch asked to be sure of: `[p, ∼p]` has four `{0,1}`
patterns and admits two. The fourth shows the same through an entailment, four of
eight. The fifth is the control — with an independent fragment all `2^{|Φ|}`
patterns appear, so the trimming is the fragment's doing and not an artefact of the
enumeration.

## Deviations from the dispatch

1. **The seeding instruction was wrong and was corrected mid-round** (the
   coordinator's correction is in `PROMPT.md`). Two further facts the correction did
   not have. *(a)* The build directory is ~50 MB, not ~400 MB, because the packages
   are symlinks into a prebuilt tree; the copy takes seconds, not minutes, and the
   background-and-poll procedure was not needed. *(b)* Repointing the symlink at
   `1fffea44` is **not sufficient**. Lake's re-clone check compares the package's
   *git remote* against the manifest URL, and the pinned cache's remote is the local
   path `/Users/anson/AgentFoundations`, not the GitHub URL the manifest names — so
   lake would have deleted and re-cloned `1fffea44` exactly as it emptied the other
   directory. Rather than mutate a shared cache, this round replaced the symlink with
   an APFS copy-on-write copy inside its own worktree and set the remote there. The
   shared caches were not written to. Any future round seeding this way will hit the
   same trap.

2. **`admissiblePatterns_sound` is stated with `coords.map (ratPayout v)`,** the
   rational payout table, rather than with `v.payout` restricted to `coords`. These
   agree by the repository's existing `payout_eq_ratPayout`, and the rational form is
   what makes the list rational; `restrictTo_payout` carries it to `v.payout`.

3. **`deductiveRegion_eq_convexHull` is stated as an image equality**,
   `restrictTo coords '' {p | deductiveRegion D coords p} = convexHull ℝ …`, and
   takes `coords.Nodup`. Membership was *defined* through the hull, so the
   unfolding form is `rfl` and says nothing; the image equality is the statement
   with content, and its surjectivity direction is where duplicate-freeness is
   actually used. The other three region theorems do not assume it.

4. **Aristotle was not used.** No leaf resisted two genuine attempts — the longest
   detour was diagnostic (below), not a proof obstacle. The log is therefore empty:
   no submissions, no returns, nothing kept.

## Two dependency constructions that do not reduce in the kernel

Both were found by bisection after `decide` failed, and both cost real time, so
they are recorded for the next round that wants kernel-checked instances over these
types. Neither is a defect: both are code written for elaboration rather than for
kernel evaluation.

1. **`finiteAtomAssignments` cannot be used under `decide`.** It indexes bit vectors
   by `Finset.sort`, which is `List.mergeSort`, whose well-founded recursion the
   kernel does not unfold. A one-atom context reduces because mergeSort returns at
   its base case; two atoms do not. This round's `contextList` filters a range
   instead — `(List.range (A.sup id + 1)).filter (· ∈ A)` — giving the same atoms in
   the same order with structural recursion only.

2. **`AssessmentProcess.deductiveContext` cannot be used under `decide`.** It is
   elaborated under `open Classical`, so its `Finset` operations carry classical
   decidability instances. `regionContext` spells the same set out so the computable
   instances are chosen. For the same reason `open Classical` is scoped in this file
   to the two lemmas that read a world as bits, rather than taken for the file.

3. **A consequence for the instances.** Foundation's `DecidableEq Sentence` is
   `hasDecEq`, built with `simp`-generated proof terms, which does not reduce either.
   So a `Finset Sentence` literal with two or more elements — which goes through
   `insert` — cannot appear in a `decide +kernel` goal. The stages in the instances
   are singletons, and the empty region is exhibited with the unsatisfiable single
   sentence `p ⋏ ∼p` rather than with `{p, ∼p}`. The same reason is why
   `witness_coords_nodup` is proved by `simp` rather than `decide`.

## What this does not establish

- **No claim is registered**, and no `PRIORITIES.md` item is filed. Both are
  reserved below.
- **Item 42 is not answered.** It asks for a polynomially presentable row family
  between the affine relations and the coherence polytope. This round supplies, in
  Lean, the vertex set that item's exact baseline is computed from; the complexity
  question is untouched.
- **No efficiency claim.** The enumerator is `2^k` in the number of atoms the stage
  and fragment mention.
- **No date-indexed statement.** The region is defined from a stage
  `D : Finset Sentence`. Using it at day `n` means passing `DP.D n`; nothing about
  monotonicity in `n` is proved, because none of the required facts uses it.
- **The `decide +kernel` instances are singleton-staged**, for the reason in §3
  above. A two-sentence stage is exhibited only through a single conjunction.
- **`deductiveRegion` is a `Prop`-valued predicate, not a decision procedure.**
  Membership of an arbitrary real price vector in a convex hull is not decided here;
  only the vertex list is.

## Outstanding maintainer actions

1. **Decide whether to register the construction, and against which item.** Either
   file a `PRIORITIES.md` item and add `CLAIMS.md` entries whose statements of record
   are the fully-qualified declaration names above, or leave this as round evidence.
   Appended to `DECISIONS.md`'s *Awaiting the author*.
2. **Rule on the provisional names**, chiefly `admissiblePatterns`. Listed in the
   pull request's "new names introduced" field and appended to *Awaiting the author*.
3. **Decide whether the two kernel-reduction traps warrant a `PRIORITIES.md`
   *Workspace friction* entry.** They are properties of the pinned dependency and
   of Foundation, not of this repository, so this round recorded them rather than
   filing against them.
