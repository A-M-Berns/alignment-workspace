# RENAME ROUND — alignment-workspace

Extends the governance architecture; AGENTS.md rules apply. Three renames in one
round, because they collide with each other and should land as one consistent
state. Verified against the public repo before dispatch: `Workstudio` appears in
21 tracked files outside `frozen/`, `prompts/`, and `.git` — including
`lean/lakefile.toml`, `lake-manifest.json`, all four `.lean` files, four scripts
under `tests/`, `checkers/registry.py`, and `.github/apply-branch-protection.sh`.
Confirm current state yourself; that list is a pointer, not a spec.

## A. The repository

`alignment-workstudio` → **`alignment-workspace`**. Rename on GitHub (the
maintainer performs the GitHub-side rename, or confirms you may via `gh`; do not
assume write scope on repository settings). GitHub's redirect from the old path
is infrastructure and stays; nothing in the repo's files memorializes the old
name, per no-negative-ontologies.

Update every in-repo occurrence of the old repo name — notably
`.github/apply-branch-protection.sh`, `SETUP_REPORT.md`, and any documented `gh
api` paths. Do not edit `prompts/` (history) or `frozen/` (immutable). The
DECISIONS.md entry for this rename is where the change is recorded.

## B. The Lean library and namespaces

`Workstudio` → **`Workspace`**, so the repo and the library agree. This touches:
`lean/lakefile.toml` (library name and any globs), `lean/Workstudio.lean` →
`lean/Workspace.lean`, the `lean/Workstudio/` directory → `lean/Workspace/`, every
`import` and namespace declaration inside the four `.lean` files
(`Workspace.Smoke`, `Workspace.Leverage.Basic`, `Workspace.Deference.Basic`), and
the scripts that reference module paths or namespace prefixes:
`tests/audit_axioms.py`, `tests/conservativity.py`, `tests/run.py`,
`tests/path_gate.py`, and `checkers/registry.py`. Also `lake-manifest.json` if the
library name appears there.

Rebuild Lean from clean and report wall time; the `lean` gate must be green before
this PR is proposed. Confirm the axiom audit still finds and audits every
declaration — a path-prefix assumption in `audit_axioms.py` that silently matches
nothing would look like a pass.

## C. The lower-level `workspace` directory (the collision)

`projects/leverage/workspace/` cannot keep that name once the repo is
`alignment-workspace` — it is the same near-collision class the original repo
rename was done to avoid. Its own `WORKSPACE.md` states what it is: a disposable,
non-authoritative forward tree, not frozen, not checksummed, not evidence; results
must be consolidated to survive.

Rename it to something that says that. **Proposed: `projects/leverage/forward/`,
with `WORKSPACE.md` → `FORWARD.md`** — it matches the tree's own description of
itself ("disposable forward workspace") and does not overload a word now used at
repo level. Per AGENTS.md rule 6 you do not coin permanent names: if the
maintainer has confirmed `forward/` at dispatch, use it; if not, implement the
rename with `forward/` and flag it in the report as the one item awaiting
confirmation, so it is one `git mv` to change.

Update references in `projects/leverage/README.md`, `PROVENANCE.md`, the
repo-level test runner that invokes this tree's suite, and anything under
`projects/leverage/` that points at it. `CONSOLIDATION_REF.md` and the frozen tree
it names are untouched.

## D. Consistency check

After A–C, no live document, script, or config outside `prompts/` and `frozen/`
should contain `workstudio` or `Workstudio` in any casing. Report the grep that
demonstrates this, and run all gates.

## Report

ROUND_REPORT.md per convention: the three renames, the full reference-update list
per rename, Lean clean-build time, confirmation that the axiom audit still matches
declarations (with the count, not just a green tick), the §D grep, and the
`forward/` naming item flagged if unconfirmed.

## Reserved to the maintainer

- The GitHub-side repository rename itself, if you lack settings scope.
- Final confirmation of `forward/`.

---
Prompt author: Claude Fable 5 (Anthropic), 2026-08-11, in a maintainer-directed
session. Dispatched by the maintainer.
