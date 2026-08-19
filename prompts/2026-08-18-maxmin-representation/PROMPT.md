Formalize Ovchinnikov's max–min representation theorem for piecewise-affine functions in Lean 4 + mathlib, in the `alignment-workspace` repository, working toward a new pull request. Partial progress is expected and acceptable; dishonest progress is not.

# Why this matters

An open PR (#41, branch `projection-enforcement`) builds an "intrinsic projection trader" whose legality rests on one externally supplied fact: that each coordinate of the Euclidean projector onto a rational polytope can be written as a max of mins of rational affine forms. That fact is currently a *hypothesis* in `lean/Workspace/Normativity/Contrib/ProjectionCompiler.lean` — taken as data, never as an axiom. Closing it in the kernel would remove the only external mathematical dependency in that PR's spine.

**Scope discipline — read carefully.** A separate concurrent pass owns PR #41 and its branch. You must:
- base your branch on `origin/main`, NOT on `projection-enforcement`;
- never modify, rebase, or push to `projection-enforcement`;
- never modify any existing file under `lean/Workspace/Normativity/Contrib/Projection*.lean`.

Your deliverable is a **self-contained development of the general theorem**, importable later. Read `ProjectionCompiler.lean` on the `projection-enforcement` branch (via `git show projection-enforcement:lean/Workspace/Normativity/Contrib/ProjectionCompiler.lean`) once, to see the shape the consumer wants — then work independently.

# The theorem

Sergei Ovchinnikov, *Max–Min Representation of Piecewise Linear Functions*, Beiträge zur Algebra und Geometrie **43** (2002) 297–302. Preprint: https://arxiv.org/abs/math/0009026

A plain-text extraction of the full paper is at
`/private/tmp/claude-501/-Users-anson/d9699bd9-e7f8-4c5d-af63-8b2053e01921/scratchpad/ovchinnikov.txt`
(read it first; if it is gone, re-fetch the arXiv PDF and run `pdftotext -layout`).

**Definition 2.1.** Let `Γ` be a closed convex domain in `ℝ^d`. `f : Γ → ℝ` is *piecewise linear* if there is a **finite** family `Q` of closed domains with `Γ = ∪Q` and `f` affine on each. The unique affine function on `ℝ^d` agreeing with `f` on a given `Q ∈ Q` is a *component* of `f`.

**Theorem 4.1(a).** Let `f` be piecewise linear on `Γ` with distinct components `{g₁, …, gₙ}`. There is a family `{S_j}_{j∈J}` of subsets of `{1, …, n}` such that
`f(x) = ⋁_{j∈J} ⋀_{i∈S_j} gᵢ(x)` for all `x ∈ Γ`.

Note: "linear" means **affine** (`h(x) = a·x + b`); continuity is *not* an extra hypothesis — the paper observes that any piecewise linear function in this sense is automatically continuous; and `J` may be taken finite since the `S_j` are subsets of a finite set.

## Proof skeleton (from the paper)

1. `H` = the hyperplanes `{gᵢ = gⱼ}` (`i < j`) that meet `int(Γ)`.
2. `T` = the connected components of `int(Γ) \ ∪H`; these are convex, and `∪T` is dense in `Γ`.
3. **Prop 2.1**: on each region the components are linearly ordered. Hence each `P ∈ T` has a unique `n(P)` with `f = g_{n(P)}` on `P`.
4. `S(P,Q)` = hyperplanes of `H` separating `P` from `Q`; `d(P,Q) = |S(P,Q)|` is a metric with: `d = 1` ⟺ adjacent (closures share a facet); `d(P,Q) = m` ⟹ there is a chain of pairwise-adjacent regions of length `m`; `d(P,Q) = d(P,R) + d(R,Q)` ⟺ `S(P,Q) = S(P,R) ∪ S(R,Q)`.
5. **Lemma 4.1**: for any `P, Q ∈ T` there is `k` with `g_k ≤ f` on `P` and `g_k ≥ f` on `Q`. Induction on `d(P,Q)`; the base case uses the common facet (`g_{n(P)} = g_{n(Q)}` on its affine span), the step uses that a function vanishing on a hyperplane and positive on one open halfspace is negative on the other.
6. **Theorem 4.1(a)**: put `S_P = {i : gᵢ ≥ g_{n(P)} on P}` and `F_P = ⋀_{i∈S_P} gᵢ`. Then `F_P = f` on `P`; Lemma 4.1 gives `F_Q ≤ F_P = f` on `P` for every `Q`; so `F = ⋁_P F_P` agrees with `f` on `∪T`, which is dense, and both are continuous.

## Findings you should start from — these are the point of the brief

**(A) Define regions as sign cells, not as connected components.** For each `h ∈ H` and each sign vector `σ : H → {+, −}`, let the cell be `{x ∈ int Γ : ∀ h, sign(g_{i(h)}(x) − g_{j(h)}(x)) = σ h}`, and let `T` be the nonempty such cells. These coincide with the connected components, but with this definition **convexity is immediate, Prop 2.1 is true by construction, and `d(P,Q)` becomes Hamming distance on sign vectors** — so item 4's properties (i), (iv), (v) collapse to symmetric-difference algebra. This choice is most of the difficulty of the formalization; do not reproduce the paper's topological definition unless you find a concrete reason to.

**(B) The two expensive leaves.** Budget your effort accordingly.
- *Density of `∪T` in `Γ`*: needs "a convex set with nonempty interior is not covered by finitely many proper affine subspaces" plus `Convex.closure_interior_eq_closure` (verify the exact mathlib name). Moderate.
- *Geodesic connectivity of the tope graph* — that any two cells are joined by a chain differing in one sign at a time. The paper gets it from a genericity argument ("choose `p`, `q` so different hyperplanes meet `[p,q]` in different points"), which in Lean means a perturbation or measure argument with no library support. **This is the genuinely research-shaped sub-lemma.** Adjacency is load-bearing: Lemma 4.1's base case uses the common facet, so you cannot weaken the chain to "some intermediate cell". If you find a route that avoids it (deletion–restriction induction on `|H|` is one candidate), that is a real result in itself — say so prominently.

**(C) A defect in the source.** The paper never states that `Γ` must be full-dimensional, but the Lemma 4.1 proof says "the full-dimensional region `P`", and with `int Γ = ∅` you get `H = ∅`, `T = ∅`, and `∪T` not dense. **Your Lean statement must carry `(interior Γ).Nonempty` or work inside the affine hull.** Record this as errata. Look for other such gaps as you go and record them the same way — this repository's culture treats source defects as findings, not embarrassments.

**(D) Mathlib has nothing here.** No hyperplane arrangements, no topes, no oriented matroids. Verify that rather than assume it (search `Mathlib` for arrangement/tope/sign-vector/oriented-matroid and for recent polytope material) — if something has landed, use it. Also search hard before proving anything: the finite closed pasting lemma for continuity, `Continuous.ext_on` for the density finish, interior of a proper affine subspace, `Convex.closure_interior_eq_closure`.

# Use Aristotle liberally

`aristotle` is on `PATH` (`/Users/anson/.local/bin/aristotle`, `ARISTOTLE_API_KEY` in env) — Harmonic's async prover backend.

```
aristotle submit --project-dir <dir> "<instructions>"     # async; returns a project id
aristotle list | aristotle show <id> | aristotle tasks <id>
aristotle download <id>
```

Guidance:
- **Offload aggressively.** Any leaf you have not closed within a couple of genuine attempts is a candidate. Submit several in parallel — they are async and independent.
- **Give it self-contained statements** with the imports and definitions it needs, in their own file under a project dir. A lemma stated against your own definitions is far more likely to come back proved than a vague goal.
- **Never tight-poll.** Check with `aristotle show` on long intervals and do other work in between.
- **Aristotle output never bypasses review.** Read every proof it returns, check the *statement* is the one you wanted, and rebuild locally. A machine proof of the wrong statement is the specific failure mode to guard against. If a returned proof is correct but grotesque, keep it and note it.
- Record what you submitted, what came back, and what you kept. That log is part of the deliverable — the user wants to know how well Aristotle handled this shape of problem.

# Repository rules (non-negotiable)

Read `AGENTS.md` and `CONTRIBUTING.md` first; they govern.

- **No `sorry` and no `axiom` in any committed Lean file.** CI enforces both (`tests/audit_axioms.py` re-elaborates every file and rejects anything outside `[propext, Classical.choice, Quot.sound]`). If a leaf will not close, either leave it out of the committed development or make it an explicit *hypothesis* of the theorems that consume it — the discipline `ProjectionCompiler.lean` already uses. **Restating the hypothesis is not progress**; the value here is in actually closing leaves, and the report must be candid about which ones you did.
- Every Lean file ends with `#print axioms` lines for its public results.
- Lean 4.31.0, mathlib pinned through `agentFoundations` (see `lean/lakefile.toml`). `lean/lakefile.toml` has `globs = ["Workspace.+"]`, so a new file under `lean/Workspace/` is built automatically — no import to add.
- Suggested home: `lean/Workspace/Normativity/Contrib/` (repo convention is `Contrib/`); pick a name that does not collide — `MaxMinRepresentation.lean` or similar. Avoid the identifier `Support` (collides with `Function.support` and `Strategy.support`) and avoid `F` for families.
- Names are provisional under `AGENTS.md` §6; say so in the file header.
- Follow mathlib style. Keep typeclass assumptions minimal. Do not add docstrings/comments/type annotations beyond what the repository's existing files carry — match their density, which is high in headers and low inside proofs.

**Gates to run before opening the PR:**
```
python3 tests/run.py                          # project runners
python3 tests/audit_axioms.py                 # re-elaborates all Lean, checks axioms
python3 -m checkers.workspace_state --check   # (--write-handoff first if it reports a stale view)
```
plus a full `lake build`.

**Round record.** The repository expects a round directory. Create `projects/normativity/rounds/<YYYY-MM-DD>-maxmin-representation/` with a `README.md` whose opening carries a one-line verdict (single line, no internal newlines — a checker matches it verbatim), register the round in `state/rounds.json` (`verdict`, `verdict_source`, `prompt`, `path`), and put this dispatch at `prompts/<YYYY-MM-DD>-maxmin-representation/PROMPT.md` with a `REPORT.md` carrying a **Model attribution** block. Copy `projects/normativity/rounds/2026-08-16-traderized-enforcement/tests/run.py` into your round's `tests/` if you add Python. Append any decision you reserve to `DECISIONS.md`'s *Awaiting the author* queue rather than leaving it in your own report.

**Commits:** each carries `Signed-off-by: A. M. Berns <ansonberns@gmail.com>` and `Model: Claude Opus 5 (Anthropic)` trailers. No `Co-Authored-By`. The PR body must have a **Model attribution** section (CI checks it exists).

# Machine load (this machine runs several agents at once)

- Run `~/.claude/scripts/resource-guard.sh check` before any heavy job.
- **Never call `lake` directly for a full build** — use `~/.claude/scripts/safe-lake.sh build <target>`, which takes a global lock and caps `LEAN_NUM_THREADS`.
- Known trap: the guard reads macOS *swap used*, which is a high-water mark and may sit above its 80% threshold for hours while the machine is otherwise idle (load ~1.5/10, memory 40%+ free). If it blocks and the machine is genuinely quiet, elaborate single files with one Lean process instead of blocking indefinitely:
  `LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/<Path>.olean <Path>.lean`
  Do not run several of those at once.
- **Seed your worktree's build state before the first build**, or you will recompile mathlib for hours. From `<your-worktree>/lean`:
  `cp -RP /Users/anson/Projects/alignment-workspace/.claude/worktrees/pr40-projection/lean/.lake/packages .lake/packages`
  then `cp -Rc /Users/anson/Projects/alignment-workspace/.claude/worktrees/pr40-projection/lean/.lake/build .lake/build`.
  Use `cp -RP` for `packages` (they are symlinks into `/Users/anson/AgentFoundations/.lake/packages` and must stay symlinks). Verify with `readlink .lake/packages/mathlib` and `ls .lake/build/lib/lean/Workspace` before building.

# Deliverable

Open a PR against `main` with a body that separates, explicitly:
- **kernel-checked** — proved here, axiom-clean;
- **source-backed** — anything still resting on a cited external statement, named exactly;
- **open** — leaves you did not close, each with the precise statement and your assessment of why it resisted;
- **errata** — defects found in the source paper.

Do not merge. Report back with: the PR URL; a table of every lemma attempted and its status; the Aristotle log (submitted / returned / kept / rejected-and-why); an honest estimate of remaining work to close the theorem; and whether the sign-cell reformulation and the deletion–restriction route panned out.

If you conclude partway that the theorem is materially harder or easier than described here, say so in the report rather than quietly adjusting scope. If you get genuinely blocked on something only the maintainer can decide, say so and keep working on everything that does not depend on it.
