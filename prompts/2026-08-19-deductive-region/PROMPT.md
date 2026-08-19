# Dispatch — the deductive coherence region as a rational vertex list

Kept verbatim as sent, per `AGENTS.md` standard 12, including what it got wrong.
The mid-round correction the coordinator sent is reproduced below the dispatch, in
the order received. Corrections to both are in `REPORT.md`.

---

## As sent

Formalize, in Lean 4 + mathlib, the finite effective construction of the **deductive coherence region** on a finite fragment, as a rational vertex list.

Repository: `A-M-Berns/alignment-workspace`. Base your branch on `origin/main`.

# READ THIS FIRST — the startup step that has killed two previous agents

Seeding the Lean build state is a multi-minute filesystem copy that produces **no output**, and the agent watchdog kills you after 600 s of stream silence. Two earlier agents died exactly there. Run it **in the background and poll**, so your stream stays alive:

```
cd <your-worktree>/lean
mkdir -p .lake
cp -RP /Users/anson/Projects/alignment-workspace/.claude/worktrees/pr40-projection/lean/.lake/packages .lake/packages
nohup cp -Rc /Users/anson/Projects/alignment-workspace/.claude/worktrees/pr40-projection/lean/.lake/build .lake/build > /tmp/seed-$$.log 2>&1 &
```
then poll every ~30 s with `du -sh .lake/build` until it stops growing (~400 MB), printing the size each time. Verify `readlink .lake/packages/mathlib` is a symlink into `/Users/anson/AgentFoundations/.lake/packages` before building. **`-RP` for `packages`** (they are symlinks and must stay symlinks); `-Rc` for `build` (APFS copy-on-write).

Without this seeding you will recompile mathlib for hours. With it, an incremental build is a couple of minutes.

# The target

Fix `DP : DeductiveProcess` (pinned dependency `Formalized-Agent-Foundations`, namespace `LogicalInduction`) and a finite fragment given as a duplicate-free `List Sentence`. Define the day-`n` region

```
K = conv { W|_Φ : W ∈ PC(D) }
```

— the convex hull of the restrictions to `Φ` of the propositionally consistent worlds satisfying the finite stage `D`.

Deliver a **finite rational vertex list** plus proofs:

```lean
def admissiblePatterns (D : Finset Sentence) (coords : List Sentence) : List (List ℚ)

theorem admissiblePatterns_sound    -- every listed pattern is `v.payout` restricted to
                                    -- `coords`, for some `v : PCWorld` with `v.ConsistentWith D`
theorem admissiblePatterns_complete -- every `v : PCWorld` with `v.ConsistentWith D` has its
                                    -- restriction to `coords` in the list
theorem admissiblePatterns_nonempty -- under the exact consistency hypothesis on `D`
theorem admissiblePatterns_mem_cube -- every entry is `0` or `1`
```

Exact spelling is yours; those four facts are the deliverable. `admissiblePatterns_nonempty` must state the **exact** hypothesis on `D` it needs — do not assume more, do not leave it implicit.

Also provide the bridge to price vectors:

```lean
def deductiveRegion (D : Finset Sentence) (coords : List Sentence) : (Sentence → ℝ) → Prop

theorem deductiveRegion_eq_convexHull      -- it is the convex hull of the listed patterns
theorem payout_mem_deductiveRegion         -- `v.ConsistentWith D → deductiveRegion D coords v.payout`
theorem deductiveRegion_fragmentLocal      -- membership depends only on the `coords` coordinates
theorem deductiveRegion_subset_cube
```

`payout_mem_deductiveRegion` is the load-bearing one: downstream it gives the enforcement trader **zero liability** at every deductively plausible world.

# The decidability you must actually construct

"Which `{0,1}` patterns on `Φ` extend to a p.c. world satisfying `D`" must be **decided**, not assumed. `PCWorld` is `LO.Propositional.Boolean.Valuation ℕ` (i.e. `ℕ → Prop`) and `v.ConsistentWith D` is `∀ φ ∈ D, v.Holds φ`. Only the finitely many atoms occurring in `D ∪ Φ` matter, so this is a finite search over assignments to those atoms. **Brute-force `2^k` enumeration is entirely acceptable** — this is about exact termination and correctness, not efficiency. **No `native_decide`.**

Search the dependency first: it has `Sentence`, `PCWorld`, `PCWorld.Holds`, `PCWorld.payout`, `ConsistentWith`, a `Compactness.lean` with an `ofBits` construction, and decidability infrastructure for propositional formulas in the vendored `Foundation`/`LO.Propositional` library. If you must build your own formula evaluator, prove it agrees with `PCWorld.Holds`.

**Watch the extension step.** A *formula* in `Φ` is not an atom: two sentences of `Φ` can constrain the same atom, so a pattern can be unrealisable for that reason alone. Stating soundness/completeness about **worlds** rather than atom assignments makes this come out right automatically.

# Rules

- **No `sorry`, no new axioms, no `native_decide`, no floats.** CI enforces the axiom bound (`propext`, `Classical.choice`, `Quot.sound`).
- Exact rational arithmetic; patterns are `ℚ`-valued (`0` or `1`) so they feed a polytope interface directly.
- Every Lean file ends with `#print axioms` for its public results.
- Lean 4.31.0. `lean/lakefile.toml` globs `Workspace.+`; put your file under `lean/Workspace/Normativity/Contrib/`.
- Read `AGENTS.md` and `CONTRIBUTING.md`; they govern. mathlib style, minimal typeclass assumptions, repository comment density (high in headers, low inside proofs). Names provisional under `AGENTS.md` §6 — say so in the header. Avoid the identifier `Support`.
- **Do not modify branch `projection-enforcement`, and do not create files named `Projection*.lean`, `RationalPolytope.lean` or `PolyhedralProjection.lean`** — another pass owns those.

**Gates:** `python3 tests/run.py`, `python3 tests/audit_axioms.py`, `python3 -m checkers.workspace_state --check` (`--write-handoff` first if stale), full build.

**Round record:** `projects/normativity/rounds/<YYYY-MM-DD>-deductive-region/README.md` with a one-line verdict (single line, no internal newlines — a checker matches it verbatim), registered in `state/rounds.json`; this dispatch at `prompts/<YYYY-MM-DD>-deductive-region/PROMPT.md` with a `REPORT.md` carrying a **Model attribution** block. Reserve maintainer items in `DECISIONS.md`'s *Awaiting the author* queue.

**Commits** carry `Signed-off-by: A. M. Berns <ansonberns@gmail.com>` and `Model: Claude Opus 5 (Anthropic)`. No `Co-Authored-By`. PR body needs a **Model attribution** section.

# Use Aristotle liberally

`aristotle` is on PATH (`ARISTOTLE_API_KEY` in env):
```
aristotle submit --project-dir <dir> "<instructions>"    # async
aristotle list | aristotle show <id> | aristotle download <id>
```
It did well on companion problems given a self-contained file (imports + your definitions + the goal with one `sorry`) plus a short outline. Offload any leaf not closed in two genuine attempts; run several in parallel; never tight-poll. **Read every returned proof and confirm the statement is the one you wanted.** Log submissions, returns, what you kept.

# Machine load

Another Lean build is running on this machine. `~/.claude/scripts/resource-guard.sh check` before heavy work. **Known trap:** the guard reads macOS *swap used*, a high-water mark that can sit above its threshold for hours while the machine is idle; if it blocks and the machine is genuinely quiet (load < 4, memory > 30% free), use a single capped `LEAN_NUM_THREADS=2 lake build <target>`. Never run two builds at once. Prefer elaborating one file at a time (`LEAN_NUM_THREADS=2 lake env lean <file>`) over full builds while iterating.

# Deliverable and honesty

Open a PR against `main`; do not merge. Report: the PR URL; exact final signatures (I will write code against them); a lemma table with status; the Aristotle log; whether the enumerator is a computable `def`; and the exact consistency hypothesis nonemptiness needs.

Include kernel-checked witnesses: one worked finite instance with the admissible patterns stated explicitly; an **inconsistent `D`** (empty region); and a `Φ` containing two sentences constraining the same atom, so not all `2^{|Φ|}` patterns are admissible. Those are the cases most likely to expose a wrong statement.

If something resists, do not weaken a statement silently. Report the exact desired declaration, the exact missing lemma, why it resists, the smallest plausible next proof, and whether the obstacle is mathematics, dependency infrastructure, or engineering. Push hard before calling anything blocked.

---

## Mid-round correction, as sent

Urgent correction to my seeding instruction — it has a bug that is destroying a shared directory. Please do this before your next `lake` invocation.

**The problem.** I told you to `cp -RP <pr40-projection>/lean/.lake/packages .lake/packages`. That copies a symlink `agentFoundations -> /Users/anson/.cache/faf-pinned/d89817bc15d23c663d0520e3a854d6d02374074d`. But your branch is based on `origin/main`, whose `lean/lake-manifest.json` pins agentFoundations at the OLD revision `1fffea44eece253cda1722568a3adfe34e822f03`. So when you run `lake`, it reconciles by checking out `1fffea44` *inside the symlink target* — which is another session's pinned cache for a different revision. It has already emptied that directory once.

**The fix.** Point your `agentFoundations` at the cache for the revision your manifest actually names:

```
cd <your-worktree>/lean
rm .lake/packages/agentFoundations
ln -s /Users/anson/.cache/faf-pinned/1fffea44eece253cda1722568a3adfe34e822f03 .lake/packages/agentFoundations
readlink .lake/packages/agentFoundations   # must print the 1fffea44 path
```

Leave every other symlink in `.lake/packages` as it is — those are shared read-only build products and are fine.

**Two standing rules for the rest of your run:**
1. **Never run `lake update`,** and do not edit `lean/lakefile.toml` or `lean/lake-manifest.json`. Your work does not need a dependency bump.
2. **Never write into `/Users/anson/.cache/faf-pinned/d89817bc15d23c663d0520e3a854d6d02374074d`.** That path belongs to another session.

If `lake` still tries to re-checkout agentFoundations after the fix, stop and tell me rather than letting it proceed — that would mean the manifest and the symlink still disagree, and I would rather diagnose it than have it clobber something again.

Nothing else about your task changes. Sorry for the misdirection; the mistake was in my instructions, not in your execution.
