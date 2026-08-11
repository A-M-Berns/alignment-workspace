# AGENTS.md — binding standards

One document, read by agents and humans alike. **Binding on every agent round run
against this repository**, and on every contribution. Agent tooling reads this
filename automatically, so a dispatched round inherits these rules without its
prompt restating them — and a round that violates one is wrong even if its prompt
did not mention the rule.

Where a rule is machine-enforced, the gate is named. Where it is not, it is a
review matter, and the table in §13 says which is which.

---

## The standards

### 1. `frozen/` is immutable

Cite it; never edit it. Frozen inputs are read-only, checksummed in
`frozen/FROZEN_INPUT_CHECKSUMS.json`, and referenced by path. A frozen input that
needed changing was not frozen: the honest move is a new dated entry beside the
old one. **Gate 3** recomputes every tree digest and refuses any pull request
touching `frozen/` that does not update `frozen/MANIFEST.md`.

### 2. Exact arithmetic

Theorem-bearing code uses exact rationals — `fractions.Fraction`. Floats appear
only in clearly-marked exploration or visualization code, and no result depends
on one. A number in a claim is exact, and the test that recomputes it compares
exactly.

### 3. A theorem ships as four things

Statement + implementation + test + necessity witnesses where feasible. **A claim
without a check is a proposal, not a result**, and must be labelled as one. Where
a necessity witness is not feasible, the statement says so; an unexamined
hypothesis is a gap, and naming it is not a failure.

### 4. Lean discipline

Sorry-free. `#print axioms` on everything. Results audit to
`[propext, Classical.choice, Quot.sound]` and nothing else. **External theory —
Logical Induction facts, corpus results, anything from another body of work —
enters as named hypotheses of the statement that uses it, never re-asserted as
axioms.** An `axiom` declaration standing in for a citation is the specific
failure this rule exists to prevent. **Gate 2** enforces all of it.

### 5. Runners

One command per project; one repo-level runner that runs them all. A project's
runner is self-contained: it reaches outside its own directory only to read
`frozen/`. **Gate 1.**

### 6. No permanent naming

Propose names; flag them; **the author decides**. A round needing a name for
something new uses an obviously provisional one, marks it, and lists it in the
round's report and in the pull request's "new names introduced" field. A name
that ships is very hard to change later.

### 7. Citation integrity

No unverified identifiers. Cite content inline, or cite a claim identifier
against a checksummed frozen path. **Never a remembered label.** If a citation
cannot be verified against the source it names, state the content directly and
record that the label did not check out.

### 8. Deviations are declared

A deviation from a prompt is declared in the round's REPORT with its reason —
**never silently absorbed, never silently "improved."** A prompt that turns out
to be wrong about a fact, a path, or a count is corrected in the report, with the
correction stated plainly. Improving a prompt's instruction without saying so is
the same failure as ignoring it.

### 9. Reports state what was not shown

With the same care as what was. Every report carries a section saying what its
work does **not** establish: which hypotheses are assumed, which evidence is
weaker than it looks, which claim rests on a reading rather than a proof.

### 10. Authoritative artifacts live on the author's machine

Agents propose changes as diffs or prompts **unless the round explicitly grants
write scope**. A round with write scope says so; without it, the deliverable is a
proposal.

### 11. Everything an agent generates is marked as such

Per the provenance discipline in §12. The round's `PROMPT.md` and `REPORT.md` are
committed under `prompts/<date>-<round>/`, with the prompt kept **verbatim as
sent** — including anything it got wrong, since a report routinely corrects its
own prompt and the correction is only legible against the original.

### 12. Dual-register documentation, and provenance

Both are below, because both are conditions on what a deliverable *is*.

---

## Dual-register documentation

**Every substantive deliverable ships both registers.** A result with only one is
incomplete, and a pull request adding results without both fails review.

**Verification register** — agent-facing, auditor-facing. Exact statements, full
hypotheses, what each test checks, how to re-verify, claim identifiers. The
`THEOREMS.md` / `VERIFICATION.md` style: precise, dense, and boring on purpose.

**Human register** — what was shown and why it matters, in plain language, with
no jargon that is not defined on the spot. The `FOR_HUMANS.md` style. Not a
summary of the other register: a different account of the same work, aimed at
someone who will not read the first.

The two registers are not redundancy. A result that cannot be stated precisely is
not finished, and a result that cannot be explained plainly is not understood.

---

## Provenance

**Three origin classes**, declared per artifact:

| class | meaning |
|---|---|
| `human` | author-written |
| `llm-reviewed` | LLM-generated; the author has done a pass and stands behind it |
| `llm-unreviewed` | LLM-generated, not yet author-reviewed |

`llm-unreviewed` **is allowed** — this is a working repository, and pretending
otherwise would just make the labels lie. But it must be labelled, and
**headline or flagship documents may not remain in that state**.

**Mechanics.** A `PROVENANCE.md` in each results directory, one line per file or
glob, carrying: origin class; generator and date; the originating round under
`prompts/`; and — where one exists — the originating chat bundle in `frozen/`.
The pull-request template asks for provenance entries added or updated alongside
new names introduced.

**The chat-bundle pointer is optional**, filled when a bundle exists and absent
otherwise. No artifact, flagship or not, is required to have one.

---

## Chat dumps

Research conversations can serve as first-class provenance. **Dumps are optional
and are produced only on author request** — not a standing requirement. Making
them standing would drag transcript overhead into every round; the value is in
deliberately bundled trails for work that warrants them. Flagship results are the
natural things to request one for, and nothing mandates it.

When the author requests a dump, it is a bundle:

```
<name>-chat-dump-<date>/
  README.md       what these conversations produced; how to navigate
  INDEX.md        one entry per conversation: date, participants (author +
                  which model(s)), topics, what came out of it
  transcripts/    the conversations, scrubbed, substance only
  artifacts/      files produced in the conversations, if not already in the repo
```

Bundles are assembled **outside** the repository, reviewed, then enter `frozen/`
like any other archive — checksummed and immutable.

### Scrubbing

Applied **before the author ever reviews**, so that review is a second pass and
not the only one.

1. **Personal identifiers and logistics** — emails, phone numbers, addresses,
   account and financial details, travel and scheduling, API keys and tokens,
   local paths exposing usernames.
2. **Personal-life content interleaved with research** — health, family,
   relationships, career deliberations. **Cut whole passages; do not paraphrase
   them.**
3. **Candid assessments of named third parties** — colleagues' abilities,
   evaluations of specific people's talks or work, mentorship characterizations.
   Technical engagement with someone's published work **stays**; frank opinions
   about persons **go**. When in doubt, cut and flag.
4. **Keep** all technical content, all decisions and their reasons, and the
   actual back-and-forth of derivations. That is the point of the bundle.
5. Every cut is marked inline as `[scrubbed]` — **no category label**, because
   labels leak the thing the cut removed.

### Release gate

A chat dump reaches a public repository **only after the author's explicit
read-through sign-off, recorded in `DECISIONS.md`**. Agents assemble and scrub;
**only the author releases.** Until sign-off, dumps live in private staging.

### Collation

The author exports or pastes the conversations and supplies them with the dump
name. The collator produces the bundle above **plus a `SCRUB_REPORT.md`** listing
every category-3 judgment call and everything borderline, for the author's review
pass.

---

## 13. Which standards are gates

| standard | enforced by |
|---|---|
| 1, frozen immutability | **gate 3** — tree digests, and the manifest rule on pull requests |
| 4, sorry-free | **gate 2** — the build, plus a textual scan |
| 4, `#print axioms` present | **gate 2** — `tests/audit_axioms.py` |
| 4, results audit to the three | **gate 2** — re-elaborates each file; also catches `sorryAx` |
| 5, runners | **gate 1** — `tests/run.py` |
| foundations stay verified | **gate 4** — the frozen consolidation's own runner, from a copy |
| 2, exact arithmetic | **not gated** — review; a float in theorem-bearing code is a finding |
| 3, theorem ships as four things | **not gated** — review; the PR template asks for each |
| 6, no permanent naming | **not gated** — review; the PR template asks |
| 7, citation integrity | **not gated** — machine-checkable only against a checksummed tree, not in general |
| 8, 9, deviations and not-shown | **not gated** — review |
| 10, write scope | **not gated** — the round's dispatch says |
| dual register | **not gated** — review; a heuristic presence check is a candidate, see `OPEN_PROBLEMS.md` |
| provenance | **not gated** — review; the PR template asks |

Six gated standards decide correctness. The rest decide fit, and that is
judgement rather than a script.
