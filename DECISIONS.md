# Decisions

Dated decision ledger. Settled decisions are recorded here and are not
re-litigated; anything awaiting the author is an explicit stub, and stubs are
listed at the top of each round's report until they are closed.

## Awaiting the author

- **Whether the leverage frozen trees are registered now or at the next leverage
  round.** `consolidation_aug9/` is registered and checksummed; the question is
  whether anything else from that line — earlier consolidations, the source
  tree's archived material — should join it now.
- **The name of the leverage forward tree.** `projects/leverage/forward/` is in
  place and its documents read in those terms; the name was proposed in the
  dispatch, not confirmed by the maintainer. It is one `git mv` and a handful of
  references to change while the tree is still small.
- **Which deference documents are canonical.** `projects/deference/notes/` is
  seeded with a pointer rather than with documents; see the note there.

## Settled

### 2026-08-11 — provenance is two fields, superseding the three origin classes

`AGENTS.md` carried both schemes at once, so the repository did not have a
provenance scheme; it had two. Resolved to **generator** plus **review status**.

The three-class scheme cannot express the case this repository is built for: an
external contribution is neither `human` in the sense meant (a maintainer wrote
it) nor `llm-reviewed` (nobody reviewed it), and calling it `llm-unreviewed`
asserts a generator nobody knows. Who made a thing and whether anyone vouches for
it are independent, and one label cannot carry both.

`ci-only` replaces `llm-unreviewed` as the ordinary honest state. Dependent
references were updated in `PROVENANCE.md`, `CONTRIBUTING.md`, `README.md` and
the pull-request template. Completed round reports keep the vocabulary that was
true when they were written; no script parsed the class names.

### 2026-08-11 — model attribution is recorded at the pull request as well

Trailers alone are invisible where attribution matters — a reviewer reads the
pull-request body, not each commit — and a squash merge composes its message from
that body, so a trailer-only record can vanish from `main` entirely. The template
now carries a **Model attribution** section and CI checks it is present and
non-empty. Like the DCO gate, it checks that an assertion was made, not that it is
true. `unrecorded` is a correct answer; a guess is not.

### 2026-08-11 — the program has no name, and a lint keeps it that way

`README.md` described the work as a program named after its two maintainers,
against the standing names-off posture. Rewritten as a description of what the
program is. **The program is not named**, and naming it is reserved.

`tests/name_lint.py` scans tracked Markdown outside `prompts/` and `frozen/` for
maintainers' personal names, exempting this ledger and anything inside backticks.
It exists because the licensing round's residue sweep reported clean while that
README line sat in plain sight: the sweep searched for change-memorial phrasing
and could not see a standing decision being violated. A decision that is only
written down gets re-violated.

**The 2026-08-10 name-and-scope entry below keeps its wording.** It is a dated
record of a decision made before the names-off posture existed, no document
depends on it, and the ledger is where history lives — which is why the lint
exempts this file rather than this file being rewritten to satisfy the lint. Two
passages in `SCRUB_REPORT.md` that the lint did catch were generalized.

### 2026-08-11 — reserved items are listed, not mentioned

A report that reserves something to the maintainer ends with **Outstanding
maintainer actions**. Prose is not enough: the rename round left the settings-side
repository rename to the maintainer, said so in the body of its report, and the
rename went unperformed while the tree already pointed at the new name.

Two round records missing from `prompts/` were reconstructed in the same round,
marked as after-the-fact rather than presented as contemporaneous. One dispatch is
unrecoverable and is recorded as unavailable rather than paraphrased into
existence.

### 2026-08-11 — the repository, the Lean library, and the forward tree renamed

Three names, settled together because they collide with each other.

The repository is **alignment-workspace** and the Lean library is
**`Workspace`**, so that the two agree: namespaces are `Workspace.Leverage.*`
and `Workspace.Deference.*`, the library root is `lean/Workspace.lean`, and the
Lake package is `workspace`. This closes the naming stub the scaffolding round
opened, and closes it at the cheapest moment — before any real development lands
in the library.

The leverage forward tree is **`projects/leverage/forward/`**, with
`FORWARD.md` as its self-description. It could not keep its previous directory
name once the repository took that word: a path whose last component matches the
repository's own name is the near-collision this rename existed to remove. The
new name says what the tree's own document already said it was — disposable,
non-authoritative, consolidated or discarded. The name itself is still awaiting
the maintainer; see the stub above.

GitHub's redirect from the previous repository path is infrastructure and stays,
so existing clones, links and the `origin` remote keep working. Nothing in the
repository's living files records the previous names; the dispatches under
`prompts/` are history and keep the names that were true when they were written,
as does git history.

### 2026-08-11 — public, and branch protection live

The repository is **public** as of 2026-08-11, and branch protection on `main`
was applied in the same sitting and verified by read-back: the eight required
checks, zero required approvals, code-owner reviews off, enforce-for-admins on,
force-pushes and branch deletion blocked. Applied with
`.github/apply-branch-protection.sh`, which reads back what GitHub stored rather
than trusting the write.

Direct pushes to `main` are now refused for everyone, maintainers included. All
changes arrive as pull requests that pass the eight gates.

**The flip was made at the maintainer's direction with the note-dump release gate
undischarged.** The bundles' conversations had not been read through for release.
A mechanical scan for emails, phone numbers, API keys and home paths came back
clean across all 51 files, but that scan cannot see the two categories only a
person can judge — personal-life passages, and candid remarks about named third
parties. Recorded here rather than left implicit, because the ledger is where
this repository keeps the things it decided to accept.

**Required approvals: zero, deliberately.** GitHub forbids self-approval, so
requiring even one approval would mechanically reinstate a two-human gate on every
maintainer pull request — precisely what this ledger decided against earlier today.
Enforcement lives in the eight required checks, not in required reviews. For the
same reason `require_code_owner_reviews` is false: with both maintainers listed as
code owners, requiring a code-owner review would reinstate the same gate by
another route.

**Enforce for administrators: on, understood as a latch and not a lock.** The
repository owner can always disable protection in settings, so this does not stop
deliberate bypass and does not pretend to. What it does is convert accidental or
lazy bypass into a visible, deliberate settings change. That is the intended
amount of self-binding, and it is the most a constitution can honestly claim
against someone holding admin rights.

**Force-pushes and branch deletion blocked**, which is what makes git history
immutable in fact rather than by convention — the frozen discipline presumes it.

**CI job names are now spec-layer values**, because required checks match them by
exact string and a rename breaks enforcement silently in either direction.


### 2026-08-11 — licence: Apache-2.0, one licence for everything

Apache-2.0 for all repository content, code and prose alike. Rationale: Mathlib
compatibility upstream; §5 makes contributions inbound-equals-outbound, which
matters for anonymous contributors; split licensing rejected as a per-file
question that never ends. No per-file headers — the root `LICENSE` governs. Any
copyright line reads "the alignment-workspace contributors", with no personal
names.

### 2026-08-11 — upstream Formalized-Agent-Foundations was already Apache-2.0

**A correction, not an action.** This round was dispatched to license FAF on the
report that it had none. That report was wrong: FAF's Apache-2.0 `LICENSE` was
added on 2026-07-29, its README already carries a licence section, and the
licensing commit is an **ancestor of the pinned commit** — so the pin has always
pointed at licensed code. The earlier finding was a shell-glob artifact that
reported absence without testing for the file.

Consequences: nothing was changed in FAF; no pin bump was made, since bumping "to
the licensing commit" would move the pin *backwards*. The pin stays at
`1fffea44eece253cda1722568a3adfe34e822f03`. Foundation was read rather than
assumed and is also Apache-2.0, so the whole solver stack is one licence.

### 2026-08-11 — DCO over CLA, pseudonymous sign-off accepted

Developer Certificate of Origin v1.1 at `DCO`; every commit signed off; CI gate 8
checks it with a script rather than a third-party app, so the gate has no
dependency the repository does not control. Pseudonymous sign-offs are accepted
deliberately: Apache-2.0 §5 is the primary rights mechanism, and a CLA would buy
little against anonymous contributors while costing every one of them a barrier.

### 2026-08-11 — external-citation norm set

Nothing may be cited externally until maintainer-reviewed, or — for registered
claims — until its epistemic class is one the citer will print alongside the
citation. External citation makes a thing flagship, and flagship content may not
remain unreviewed.

### 2026-08-11 — model attribution required

Commits whose content is substantially AI-generated carry `Model:`, and where the
prompt author differs from the executor, `Prompt-author-model:` as well. Round
reports carry an attribution block. Applied retroactively without rewriting
history: `PROVENANCE.md` was corrected instead — and the correction included a
factual error, since earlier rows named the executor as "Claude Opus 4.6" when it
was Claude Opus 5 throughout.

### 2026-08-11 — second maintainer, and co-equality

Abram Demski (`abramdemski`) joins the maintainer set, in `CODEOWNERS` and
`tests/path_gate.py`, each pointing at the other with the rule that the two must
agree. Maintainers are co-equal: any maintainer's review satisfies a
maintainer-review requirement, **including self-review**, with the dated ledger
entry as the review record. **No two-human gates anywhere.** At this scale the
ledger and git history are the accountability mechanism, and a repository owner's
admin rights make a self-binding two-human rule unenforceable anyway.

This partially amends the names-off posture: maintainer handles are necessarily
public in a public repository. Prose-level anonymity of the program is unchanged.

### 2026-08-11 — the deference line carries its own name

The line is **deference**, everywhere current: directory, Lean namespaces
including `Workspace.Deference.Kernel`, registries, path gate, problem pointers,
prose. Completed round records keep the names that were true when written, as
does git history — those are records, not living documents. Frozen trees were
untouched and already carried the right name.

### 2026-08-11 — no negative ontologies

Living documents and structures describe the present ontology only. History lives
in exactly two places — git history and this ledger — and nowhere else. No
"formerly", no "(previously X)", no "migrated from" residue. A live pointer that
carries current epistemic content, such as a registry `superseded-by` link, is
not residue and stays.

Applied retroactively in the same round: a sweep of living documents found **no
genuine residue**. The only matches were the principle's own statement of itself
and retired material under `attic/`, which is history by construction.

### 2026-08-11 — the third-party reference payloads are cited, not vendored

The note dumps' `references/` payloads were removed and replaced by the frozen
entry `references-citations-2026-08-11`, which pins each removed file by sha256
alongside its bibliographic entry. The repository has no redistribution rights to
published papers; arXiv's default licence lets arXiv distribute and grants
nothing to third parties. The bundles' conversations, notes and Lean content are
untouched, and the change went through the sanctioned frozen procedure: new dated
entry, superseded entries annotated, digests recomputed together.

One citation could not be verified against a publisher of record. It is flagged
as unverified inside the entry rather than reconstructed from memory.


### 2026-08-10 — repository name and scope

**alignment-workspace**: the working monorepo for the Berns–Demski research
program. It holds multiple research lines, exact-arithmetic model work per line,
one shared Lean project, frozen inputs, and dispatch provenance. Two lines at
the outset: **leverage** (the normativity and answerability program) and
**deference** (the deference and corrigibility program).

Created by renaming and repointing the existing repository rather than starting
fresh, so its history is preserved: the August 9 consolidation and its two
freeze tags predate this scaffolding and remain reachable.

### 2026-08-10 — Formalized-Agent-Foundations pinned by commit

Pinned at `1fffea44eece253cda1722568a3adfe34e822f03` — the current `main` of
https://github.com/A-M-Berns/Formalized-Agent-Foundations, whose most recent
change bumped its pinned dependencies and unforked Foundation, which is what
made it pinnable. Toolchain matched to FAF's exactly: `leanprover/lean4:v4.31.0`.

### 2026-08-10 — one Lake project, not one per line

A single Lake project at `lean/`, library `Workspace`, with per-line
namespaces. The alternative — a project per research line — would have meant a
separate dependency pin and a separate toolchain per line, and the first time
the two lines shared a definition it would have meant a fourth package to hold
it. One project keeps the solver stack consistent by construction.

### 2026-08-10 — one dependency pinned, the rest inherited

Only FAF is pinned directly. Mathlib and Foundation arrive transitively through
it. Pinning all three independently would let this repository and FAF disagree
about Mathlib, which is the failure mode the single pin removes.

### 2026-08-10 — binding standards live in `AGENTS.md`

One document, read by agents and humans alike, replacing a separate conventions
file: agent tooling reads that filename automatically, so every dispatched round
inherits the standards without its prompt restating them. The reader-facing rules
became the opening section of `CONTRIBUTING.md` rather than a separate document.

Twelve standards, of which six are machine-enforced by the CI gates and the rest
are review matters; `AGENTS.md` §13 says which is which, so nobody mistakes a norm
for a gate. The standards: exact arithmetic; what a theorem
ships as; runners; frozen inputs immutable; citation integrity; naming reserved
to the author; dispatch provenance; and the Lean discipline — sorry-free,
`#print axioms` per file, results auditing to
`[propext, Classical.choice, Quot.sound]`, and external theory entering only as
named hypotheses rather than as axioms.
