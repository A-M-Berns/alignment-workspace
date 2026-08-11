# Provenance — repository scaffolding

Two fields per artifact, per `AGENTS.md`: **generator** — who produced it — and
**review status**, `maintainer-reviewed` or `ci-only`. Where the generator is a
model, the model is named; where the prompt author and the executor differ, which
is the normal case for a dispatched round, both are named in *Round attribution*
below.

**Everything here is `ci-only` unless a row says otherwise.** That is not a hedge
— it is the accurate label, and the repository would rather carry an honest one
than a flattering one. `maintainer-reviewed` is rare by design; see `AGENTS.md`
on where human judgment is spent.

**Correction, 2026-08-11.** Earlier rows in this file named the executor as
"Claude Opus 4.6". That was wrong; the executor was **Claude Opus 5 (Anthropic)**
throughout, and the rows are corrected below. The prompts for every round were
authored by **Claude Fable 5 (Anthropic)** in maintainer-directed sessions, which
earlier rows did not record at all.

| file or glob | generator | review status | date | round |
|---|---|---|---|---|
| `README.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | `prompts/2026-08-10-repo-scaffolding/` |
| `AGENTS.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `CONTRIBUTING.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `DECISIONS.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same — **decisions are the author's; this file records them, and its wording is not the author's** |
| `PRIORITIES.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same — items 1–6 restate the frozen consolidation's own list; 7–9 quote the deference audit's §3 by section; 10–11 are proposed by this round |
| `PROVENANCE.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | same |
| `.github/**` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `tests/**` | Claude Opus 5 | `ci-only` | 2026-08-10 | same — the gate scripts; their behaviour is checked by CI, their design is not reviewed |
| `lean/lakefile.toml`, `lean/lean-toolchain` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `lean/Workspace/**` | Claude Opus 5 | `ci-only` | 2026-08-10 | same — the smoke test and the two namespace roots; **machine-checked**: they build and audit to the three standard axioms |
| `projects/*/README.md` | Claude Opus 5 | `ci-only` | 2026-08-10 | same |
| `projects/leverage/forward/**` | mixed — predates this repository | `ci-only` | — | predates this round; carried over unchanged from the source tree |
| the four consolidated trees | **`agent-consolidated`** | — | — | received or consolidated work that predates this repository; each carries its own `ORIGIN.md` with the digests at intake, and its own internal provenance |
| `prompts/*/PROMPT*.md` | the maintainer, or a model in a maintainer-directed session | `maintainer-reviewed` — dispatched as written | 2026-08-10 | verbatim as dispatched, including anything they got wrong |
| `prompts/*/REPORT.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | same |
| `projects/deference/notes/*.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | `prompts/2026-08-11-deference-corrigibility/` — the four canonical deference documents; the decision that they are canonical is the maintainer's, recorded in `DECISIONS.md` |
| `tests/path_gate.py` | Claude Opus 5 | `ci-only` | 2026-08-11 | same — one specification pattern and three self-test cases, on explicit maintainer authorization for this trust-chain file; the rest of the file predates the round |
| `PRIORITIES.md` items 14–20 | Claude Opus 5 | `ci-only` | 2026-08-11 | same — filed at the maintainer's direction to authorize the first deference wave |
| `prompts/2026-08-11-faithful-acceleration/**`, `-deference-finite-kernel/**`, `-deference-certificates/**`, `-deference-channel/**`, `-deference-densification/**`, `-deference-triangle/**`, `-deference-admissibility/**` | Claude Opus 5 | `ci-only` | 2026-08-11 | the seven wave-1 tracks, each dispatched by `prompts/2026-08-11-deference-corrigibility/`. Six executors were blocked by tooling from writing their own `.md` reports; those files are the executor's text placed by the orchestrator, and each report records it as a deviation. Where a human register was owed and the executor could not write it, the file is the **orchestrator's** text and says so at its head |
| `lean/Workspace/Deference/Contrib/**` | Claude Opus 5 | `ci-only` | 2026-08-11 | per-file rows in that directory's own `PROVENANCE.md` — **machine-checked**: builds against the pinned toolchain and audits to the three standard axioms, no `sorry`, no `axiom`. Reached by the default build target, which globs the library. Not registered. Two declarations remain `unverified-nonvacuous`, shipping no term inhabiting their full hypothesis package: `FaithfulAcceleration.weight_not_divergent` and `MagnitudePrediction.squaredError_bdd_of_sharpness_bdd` |
| `prompts/2026-08-11-phase-ii-*/**`, `prompts/2026-08-11-corrigibility-phase-ii/**` | Claude Opus 5 | `ci-only` | 2026-08-11 | the five Stage II tracks and the parent round. **Two reports are not their track's own**: `phase-ii-certificate/REPORT.md` and `phase-ii-promotion/REPORT.md` are independent verification registers authored by the closure pass, because those executors persisted no report and no draft of their prose exists. Each says so at its head and distinguishes verified artifact from reconstructed statement |
| `projects/deference/notes/FINITE_MODEL_SKELETON.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | `prompts/2026-08-11-corrigibility-phase-ii/` — **v2**, superseding v1; the amendment and the reasons are in `DECISIONS.md` |
| `projects/deference/notes/FUD_COMPARATOR_SPEC.md`, `prompts/2026-08-11-stage-iii-fud/**` | Claude Opus 5 | `ci-only` | 2026-08-11 | the Stage III round. Its Track F adversarial review was run in a **separate Claude Opus 5 context** with no access to the round report, per the dispatch's independence requirement |
| `projects/deference/notes/FUTURE_AGENT_SPEC.md`, `prompts/2026-08-11-stage-iv-future-agent/**` | Claude Opus 5 | `ci-only` | 2026-08-11 | the Stage IV round, whose construction **collapsed**; the specification is kept as a corrected defective record and the claimed-gate harness was deleted rather than repaired. Its adversarial review ran in a **separate Claude Opus 5 context** |
| `RESEARCH_STATE.md`, `prompts/2026-08-11-workspace-ethos/**` | Claude Opus 5 | `ci-only` | 2026-08-11 | the workspace ethos pass. Framing only: it names distinctions the repository already draws and adds no gate, no registry and no metadata requirement. The layer semantics it states are read off `AGENTS.md` and `DECISIONS.md` rather than legislated by it |
| the gate-count and job-name corrections in `README.md`, `CONTRIBUTING.md`, `AGENTS.md`'s gates table and `projects/leverage/CLAIMS.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | same — dead pointers left by the `frozen/` retirement: a command naming a deleted script, a retired job name, and a count of eight gates where seven run |
| `PRIORITIES.md` — the *Where ingenuity is the bottleneck* and *Workspace friction* sections, and the status marks on items 14–21 | Claude Opus 5 | `ci-only` | 2026-08-11 | same — added on maintainer instruction during the round, which is the authorization for a specification-layer change the dispatch did not scope. No item renumbered or removed; the two new sections use `### Q<n> —` and `### F<n> —` headings so the registry's item parser cannot read them as filed items |
| `AGENTS.md` — standard 14, the stronger form of *no negative ontologies*, and slop-discipline point 7 | Claude Opus 5 | `ci-only` | 2026-08-11 | same — added on maintainer instruction during the round. None is gated; all three are review matters, and the gates table is unchanged |
| `projects/deference/notes/TERMS.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | `prompts/2026-08-11-workspace-ethos/` — a recording table, not a naming act: meanings and owning documents for vocabulary already fixed elsewhere. Every term stays provisional under standard 6. The line's canonical set is five documents; the decision is the maintainer's, in `DECISIONS.md` |
| `tests/path_gate.py` — `RESEARCH_STATE.md` added, `GOVERNANCE_REPORT.md` removed | Claude Opus 5 | `ci-only` | 2026-08-11 | `prompts/2026-08-11-workspace-ethos/` — a trust-chain edit on explicit maintainer authorization, with one self-test case. Both directions only remove or relocate contributor write access |
| the front-door pass: `README.md`, `projects/deference/README.md`, `RESEARCH_STATE.md` *Where the lines stand*, `.github/PULL_REQUEST_TEMPLATE.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | `prompts/2026-08-11-workspace-ethos/` — ethos pass II. The two landing pages rewritten as current orientation surfaces; a per-line current-state section added to `RESEARCH_STATE.md`; a checklist line naming the deleted `tests/check_frozen.py` replaced. No research claim originates in any of them: the deference section is compressed from that line's own ledger and roadmap and defers to them |
| stale-count repairs in `projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md` and `TERMS.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | same — both asserted **155 theorems across 10 files** for `Contrib/`, which holds 8 files and 167 theorem or lemma declarations. Replaced with count-robust wording rather than a new number, since the load-bearing count is the number registered, which is zero |
| `.github/apply-branch-protection.sh`, `CONTRIBUTING.md` *Review*, `AGENTS.md` *Security* | Claude Opus 5 | `ci-only` | 2026-08-11 | `prompts/2026-08-11-workspace-ethos/` — auto-merge on full green, decided by the maintainer. The script gains the repository-setting call and a read-back of it, and its required-check count is now derived from the payload rather than the literal `8`, which had been stale since `frozen-integrity` was retired and would have reported correct protection as wrong |
| the attention rulings in `AGENTS.md`, `PROVENANCE.md`, `CONTRIBUTING.md`, `PRIORITIES.md`, `RESEARCH_STATE.md` and `DECISIONS.md` | Claude Opus 5 | `ci-only` | 2026-08-11 | same — three maintainer rulings taken during the round and recorded as a dated `DECISIONS.md` entry: the flagship rule retired, external citation restated to stand alone, and item filing opened to maintainer-dispatched rounds within their scope. Naming stays reserved. `DECISIONS.md`'s *Awaiting the author* becomes the single queue for reserved items |

## No originating chat bundle

The chat-bundle pointer is optional and none exists for this round: no dump has
been requested or assembled. If one is later produced for this work, it enters
the line it belongs to under the release gate in `AGENTS.md`, as an
`agent-consolidated` tree, and this table gains the pointer.

## What "machine-checked" does and does not cover here

The Lean files are machine-checked in the strong sense: they compile and their
axiom audit is clean. The gate scripts are machine-*exercised* — CI runs them and
they pass — but that is evidence they run, not that they check the right thing.
Nobody but their generator has yet read them with an eye to whether the rule they
implement is the rule intended. That is a review item, and it is exactly the kind
of thing this file exists to make visible.


## Round attribution

| round | prompt author | executor | dates |
|---|---|---|---|
| `2026-08-10-repo-scaffolding` (v1, v2, addendum) | Claude Fable 5 (Anthropic) | Claude Opus 5 (Anthropic) | 2026-08-10 – 2026-08-11 |
| `2026-08-10-contribution-architecture` | Claude Fable 5 (Anthropic) | Claude Opus 5 (Anthropic) | 2026-08-11 — **no round record survives**: the dispatch was never preserved and the report was removed as superseded. What the round installed is in `checkers/`, `tests/path_gate.py` and the ledger |
| `2026-08-11-licensing-dco-citation` | Claude Fable 5 (Anthropic) | Claude Opus 5 (Anthropic) | 2026-08-11 |
| `2026-08-11-deference-corrigibility` (wave 1) | GPT-5.6 Sol (OpenAI) | Claude Opus 5 (Anthropic) | 2026-08-11 |
| `2026-08-11-corrigibility-phase-ii` and its five tracks | GPT-5.6 Sol (OpenAI) | Claude Opus 5 (Anthropic) | 2026-08-11 |
| `2026-08-11-corrigibility-phase-ii` (Stage II closure and integration pass) | GPT-5.6 Sol (OpenAI) | Claude Opus 5 (Anthropic) | 2026-08-11 |
| `2026-08-11-stage-iii-fud` | GPT-5.6 Sol (OpenAI) | Claude Opus 5 (Anthropic) | 2026-08-11 |
| `2026-08-11-stage-iv-future-agent` | GPT-5.6 Sol (OpenAI) | Claude Opus 5 (Anthropic) | 2026-08-11 |
| `2026-08-11-workspace-ethos` | GPT-5.6 Sol (OpenAI) | Claude Opus 5 (Anthropic) | 2026-08-11 |

Rounds predating this repository's provenance discipline — the consolidation and
completing passes now frozen under `projects/leverage/consolidation-aug9/` — have
`executor: unrecorded` rather than a guess. Their prompts were maintainer-supplied
and their reports state what was done; the model that executed them is not
recorded in a form this file can honestly assert.
