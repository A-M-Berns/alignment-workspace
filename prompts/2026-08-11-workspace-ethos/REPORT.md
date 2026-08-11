# Report — workspace ethos pass

**Prompt author:** GPT-5.6 Sol (OpenAI). **Executor:** Claude Opus 5 (Anthropic).
**Date:** 2026-08-11. **Write scope:** granted for framing, extended twice by
maintainer instruction during the round — to `PRIORITIES.md` and to two prose
rules in `AGENTS.md`. No research claim, theorem, epistemic class or definition
was changed. Eight item *status marks* were added on that authorization; no item
was filed, retired or renumbered.

## What the repository already did, and was reused rather than rebuilt

Most of what the dispatch asks for exists here in substance. Reusing it was the
larger part of the work.

- **Adoption mechanism** — a dated `DECISIONS.md` entry, with self-review by a
  co-equal maintainer explicitly sufficient. No approval process was invented.
- **Precedence** — already stated three times: ledger over roadmap on whether
  something is established, registry over prose on what is established here,
  `PRIORITIES.md` over GitHub issues on what is wanted.
- **Deprecation** — *no negative ontologies* plus `DECISIONS.md` plus the
  registry's `superseded-by`. A superseded round record is not annotated by
  design, and that design is right; no deprecation registry was added.
- **Evidence strength** — the epistemic classes, `inherited-established` versus
  `workspace-established`, `architected`, `unverified-nonvacuous`, and the
  generator/review-status split. Nothing here needed a parallel scheme.
- **Per-object gap lists** — `FINITE_MODEL_SKELETON.md` §8, "what this version
  deliberately does not fix", eight numbered holes each marked as a hole rather
  than an oversight. This is the aspiration/construction distinction already
  being done well, one object at a time.
- **Provisional naming** — skeleton §9 lists twenty-two working names, none
  proposed for permanence.
- **Retirement with its reason** — every major reversal on the deference line
  carries the mechanism that forced it. That is the property this pass most
  wanted and least needed to add.

## A. What was changed

**`RESEARCH_STATE.md`**, new, at the root. The three layers mapped onto the
artifacts that already carry them; precedence including the rule for a lab result
that refutes a canonical one; aspirational/constructed/gap on both registers with
the fully-updated-deference movement worked through; seven research-debt kinds
each anchored to a live instance; consolidation triggers and the recovery test;
two report conventions; the supplies/does-not-supply interface examples. Its
closing section states its scope: vocabulary and precedence, read by people and
agents and by nothing in CI, with no list that needs synchronising.

**`AGENTS.md`**, four changes. `agent-consolidated` now says explicitly that it
is a handling status and does not say whose judgment a document carries, with the
two questions it is confusable with routed to `DECISIONS.md` and `PROVENANCE.md`.

Three further changes were made **on maintainer instruction mid-round**, which is
the authorization for them: two prose rules, and standard 14 below.

*No negative ontologies* gains its stronger form: do not define the present by
narrating an absence. The existing rule banned residue in names and structure;
this bans the sentence-level version — "we no longer do X", a section explaining
what a document is not because it once was — which compounds faster because prose
has no length limit. It ships with a test that keeps the two legitimate cases:
does the sentence work for a reader who has never heard of the absent thing?
Disambiguating two *currently live* senses passes; so does a `superseded-by`
pointer, which carries current epistemic content.

*Slop discipline* gains a seventh point, **no rules-perseveration**: follow the
standards, do not narrate following them. Its test — is this a fact a later
reader needs about the work, or a fact about the writing of it? — is what keeps
it from eating the declarations the standards require, since deviations, what was
not shown, outstanding actions and provenance are all facts about the work. The
stated reason for the rule is that compliance narration reads as evidence of
rigour and is not.

Both were applied to this round's own output: `RESEARCH_STATE.md`'s closing
section was rewritten from a list of what it is not into a statement of scope,
and its `agent-consolidated` note now leads with what the status is.

**`prompts/README.md`**, one section. Round records are evidence; a later ruling
governs; a report being newer than the ledger row it bears on does not reverse
that, it means the row is not updated yet.

**`README.md`**, one sentence naming the new document in the layout section.

**Four dead pointers repaired**, left by the `frozen/` retirement. `README.md`
and `CONTRIBUTING.md` instructed readers to run `tests/check_frozen.py`, which
does not exist; both claimed eight gates where seven run; `CONTRIBUTING.md` and
`projects/leverage/CLAIMS.md` named the retired job `foundations-verification`
rather than `consolidation-verification`; `AGENTS.md`'s gates table closed on
"eight jobs".
`.github/branch-protection.json` is the source of truth and lists seven.

**`PRIORITIES.md`**, a standing section — *Where ingenuity is the bottleneck* —
**added on maintainer instruction mid-round**, which is the authorization for a
change to this file that the round otherwise had no scope to make. It is the one
part of the file that is not a work order: a numbered item is a request for
execution, and these are requests for an idea. Seeded with four questions read
off the existing record and no new research — the near-indifference leakage, the
grade-to-quantity relation, the register that would price who holds
authorization, and the time-indexed `A`-valuation family with the two holes
beside it. The section's own rule is that an entry graduates by becoming a
numbered item, which is why the leverage line has no entries: its hard problems
are open with known shapes and are filed as items 1 and 2. Headings are `### Q<n>
—` rather than `### <n>.` so that `checkers/registry.py`, which resolves
`answers_item` against `^###\s+(\d+)\.`, cannot mistake a question for a filed
item. Verified: the registry gate still resolves three entries and the item set
is unchanged.

**`RESEARCH_STATE.md`**, a matching section stating the convention and its
diagnostic — most entries are model or assumption debt, because theorem debt is
dispatchable and debt that is not yet theorem debt is usually waiting on an idea
rather than on labour.

**Status marks on `PRIORITIES.md` items 14–21**, on maintainer authorization,
which discharges what had been proposed delta 2. All seven wave-1 items are
marked *returned wave 1*; item 20 additionally *superseded by item 26*; item 21
*answered by Stage II; the magnitude target is retired*. The section gains a
paragraph saying what the mark means and does not mean — it records dispatch
history, not that the science is settled, and several returned negative or
partial. No item was renumbered or removed, so `answers_item` resolution is
unaffected; item 13's existing `*satisfied, kept open*` supplied the form.

**A second standing section, *Workspace friction***, and `AGENTS.md` **standard
14** obliging a round to use it: structural defects are reported, not worked
around, because a workaround leaves nothing behind and the next round pays the
same cost unknowingly. Reporting is the obligation and fixing is a maintainer
decision, with one exception — a dead pointer is a fact rather than a design
question and is repaired in place. Seeded with five defects this pass hit: the
path gate's permissive default for new root documents; the absence of any check
that a documented command names a file that exists; and three consequences of
maintainer throughput, below.

**`RESEARCH_STATE.md`**, the attention paragraph. The maintainer writes in few
places and does not read most of what is produced here. That is recorded as a
design parameter rather than a backlog: `ci-only` is the standing condition of
almost everything, `maintainer-reviewed` is rare and deliberate, and the judgment
is spent on naming and on what is worth proving rather than on reading prose for
approval. Two standing rules were written on the opposite assumption, were filed
as friction, and were **ruled on by the maintainer during the round** — see the
next section.

**Three rulings landed during the round**, and the documents were changed to
match rather than left describing rules that no longer hold. The flagship rule is
retired from `AGENTS.md` and `PROVENANCE.md`; external citation is restated to
stand on its own, requiring that a citation carry the status the thing actually
has; and a maintainer-dispatched round may now file `PRIORITIES.md` items within
its own scope, with demand-gating and reserved naming otherwise intact. The dated
entry is in `DECISIONS.md`, the friction entries were retired or narrowed, and no
residue of the retired rule was left in a living document.

**One queue.** `AGENTS.md` §10 now requires a reserved item to be appended to
`DECISIONS.md`'s *Awaiting the author* rather than left in the round's own
report; the ledger's header says the same; and the section is populated, at six
entries, each with what deciding it costs. Four competing sources of reserved
items existed and none answered "what needs me?".

**Six further rulings, taken against the populated queue and performed**, which
emptied it to one entry: prose is not externally citable and asking the
maintainers is the mechanism; `RESEARCH_STATE.md` becomes specification layer;
the governance report moves to `prompts/2026-08-10-contribution-architecture/`;
the deference line gets `TERMS.md`; the leverage forward tree keeps its name; and
further leverage trees are frozen at the next leverage round rather than now.
Two of those had live pointers to repair — the moved report was **both
dual-register documents** of a registered claim — and no claim changed class.

**Four more rulings**, on the questions carried out of the contribution-architecture
round: auto-merge on full green; the checker harness ships unread, recorded as a
decision rather than an omission; the resource budgets confirmed; and the permissive
path-gate default confirmed, with the enumeration itself explicitly **not**
re-approved, since it has changed repeatedly since that report proposed it.

Auto-merge is GitHub-native rather than a workflow, and that is forced rather than
chosen: a merging bot needs write scope, and *CI holds zero secrets, permanently* is
not a rule to spend on convenience. Implementing it surfaced a stale literal —
`.github/apply-branch-protection.sh` required exactly eight required checks and the
payload has carried seven since `frozen-integrity` was retired, so the verifier would
have reported correct protection as wrong. It now counts what the payload declares.

**`PROVENANCE.md`**, rows for the above and a round-attribution line.

## C. Deference case study — the ten stress-test questions

Answered against the line as it stood before this pass. Where the answer is now
different, that is said.

1. **Aspirational versus constructed** — yes, and better than the dispatch
   assumes. The ledger says "not derivable", "retired", "empty rather than
   false", "not well-posed as attempted". The cost is that it is carried in prose
   across three hundred-odd lines and has to be reassembled on each read.
2. **Mathematical versus philosophical aspiration** — yes, and this is the line's
   strongest habit. Fully updated deference carries a deflationary gloss with the
   stronger reading marked unsupported; the non-preemption impossibility is
   labelled fatal read as jurisdiction and correct read as autonomy. It was never
   named as a convention, so a new track has nothing prompting it to do the same.
3. **The current human-canonical position** — **no, not reliably, and this was
   the largest category error available.** The roadmap and the ledger open by
   calling themselves canonical; `PROVENANCE.md` records them `ci-only`. Both are
   true and they answer different questions — which document governs, versus
   whether anyone read it — and nothing said so. Fixed.
4. **What is merely an agent synthesis** — same defect, same fix. The layer table
   now says it; the four line documents still do not carry the pointer
   themselves, which is proposed delta 2.
5. **Historical failed routes** — yes within the ledger, which records each
   retirement with its reason. The exposure is `prompts/`: a reader arriving at
   `phase-ii-certificate/REPORT.md` by path meets a strict-minority gloss that a
   later ledger entry refutes with an exact counterexample, and the report is
   correctly not edited. `prompts/README.md` now states the rule.
6. **Dominant debt types** — no, because everything unresolved was `open` or
   `blocked`. Now nameable: this line's dominant debts are **assumption**
   (item 25's near-indifference leakage, which makes the surviving competence
   candidate's bound vacuous unbounded) and **model** (the skeleton's `FU[g]`
   hole, and no operation reassigning the authorization relation at a later
   index), with **interpretation** debt on three reserved `maintainer-decision`s.
7. **The next controlling question** — yes, unambiguously, and it moved *during*
   this pass without becoming ambiguous: the Stage III ruling withdrew the
   round's positive reading, so the recommended dispatch went from item 25 alone
   to items 25 and 27, and both the ledger and `DECISIONS.md` say which and why.
   Best-signposted thing on the line, and the reversal is the evidence for that
   rather than against it.
8. **Which results are formal, finite-verified, report-level, architectural or
   assumed** — yes, mechanically. "155 theorems kernel-verified and unregistered,
   and those are different things" is the model sentence.
9. **Human review surfaces without reading every track** — partly. They are in
   four places: `DECISIONS.md`'s *Awaiting the author*, `GOVERNANCE_REPORT.md`'s
   own list, each report's *Outstanding maintainer actions*, and the
   `maintainer-decision` rows in the ledger. No single view. Collecting them into
   one would be a fifth list, so this is left as a convention rather than a file.
10. **Why the program changed its mind** — yes, and this is the repository's best
    property. Every reversal carries its mechanism: regret bounds are equivalent
    to the conclusion they were meant to buy; trader net worth is affine in
    settlement and absolute value is not; the valuation register prices whose
    selection authorises and never who holds the right.

**Worked debt-transition example, all three already on the record.** Choice-level
competence was theorem debt, and the finding that every regret-bound form is
*equivalent* to its conclusion makes the request ill-posed — model debt, and the
vocabulary had to change. The certificate's non-preemption impossibility moved
from theorem debt to interpretation debt: same mathematics, reread as a bound on
autonomy. Fully updated deference moved from theorem debt to apparent assumption
debt and then, under adversarial review **during this pass**, to model debt: the
transferred arm contained no distinct future agent, so there was no question for
an assumption to answer. All three read as failure under `open`/`blocked` and as
progress under the debt vocabulary.

## D. Proposed canonical delta

Three of the five were ruled on during the round and performed; see the dated
`DECISIONS.md` entry. Two remain proposed.

1. **One line at the head of each deference `notes/` document** separating
   "canonical for this line" from review status. Not done: those files carried
   in-flight edits from two deference rounds throughout this pass.
2. **Whether the ledger absorbs the state shape** as a header section, so the
   live deference state is recoverable in forty lines rather than six hundred.
   The cheapest available reduction of the line's compression debt.

## E. Deferred structural ideas

Recorded, not built. None has a present concrete need.

- **Machine-readable claim graph, objection edges, theorem-to-paper dependency
  map.** The hook exists — `CLAIMS.md` entries already carry `answers_item` and
  the schema has room for `superseded-by` — so an edge is a field away when
  demand appears. It has not: the deference line has no `CLAIMS.md` at all, so a
  graph would currently be over an empty set while the line's 155 kernel-verified
  theorems sit unregistered. Registration is the prerequisite, not the graph.
- **Formal amendment objects for canonical changes.** A dated ledger entry
  already does this and reads better.
- **A public challenge interface.** `CONTRIBUTING.md` already specifies the
  format — a counterexample, a failing test, or a precise objection against a
  named item — and GitHub issues carry it. A dedicated surface waits for traffic.
- **A per-line frontier document.** Would desynchronise with the ledger, which
  wins on precedence. Delta 6 proposes absorbing it instead.

## F. Procedural-bloat audit

Considered and declined, with the reason.

- **A status header on every research note.** The dispatch's own prohibition, and
  it would tax exactly the exploration the lab layer exists to make cheap. Layer
  is derivable from location.
- **A `FRONTIER.md` per line.** A fifth list to keep in sync with four that
  already exist. Absorbed into the ledger as a proposal instead.
- **A deprecation registry, and `SUPERSEDED BY:` headers on round records.**
  *No negative ontologies* deliberately keeps supersession in the two places
  history lives. Annotating reports would put it in a third and re-open the
  question of who updates them.
- **Debt words for formalization and verification.** Both already have names
  here — the standing Lean-port item family and the class ordering; and
  `unverified-nonvacuous`, unregistered, `ci-only`. A second vocabulary for the
  same facts is the parallel machinery the dispatch warned against. Seven kinds
  survived, not nine.
- **Numeric debt scores.** Classification is the point; a number would imply a
  comparison nothing supports.
- **A CI gate for layer or aspiration metadata.** There is no rule here to
  enforce, and this repository's own record shows a gate that matches nothing is
  indistinguishable from one that works.
- **A maintainer-review queue file.** Four sources of review surfaces exist; a
  fifth that must be synchronised by hand is the one that goes stale.
- **An adversarial-review requirement per theorem.** Kept as a norm. The line
  already runs independent adversarial contexts where it matters — Stage III's
  Track F ran with no access to the round report — and mandating it would price
  out cheap rounds.

## Deviations from the dispatch

1. **The dispatch's layer name "Agent-Consolidated State" was not adopted as a
   label.** `agent-consolidated` already means something else here — a handling
   status attaching to material at any layer, including the leverage line's
   authoritative record — and importing the dispatch's sense would have created
   the confusion the pass exists to remove. The layer is called *consolidated
   view*, and the collision is stated explicitly in both documents.
2. **§5's state shape, §11's symbol table and §12's interface table were not
   installed as line documents.** The four deference `notes/` files carry
   uncommitted Stage III edits; adding this pass's changes to them would make
   neither diff attributable, which §17 forbids in substance. §12's content is
   demonstrated in `RESEARCH_STATE.md` from material quoted out of the roadmap;
   §5 and §11 are deltas 6 and 5.
3. **`tests/path_gate.py` was not edited**, though the new document currently
   lands in the proof layer. §17 names path gates as avoid-unless-clearly-safe
   and it is a trust-chain file. Outstanding action 1.
4. **The pass went slightly beyond framing** to repair four dead pointers, on the
   ground that a command naming a deleted script is a defect in the contributor
   onboarding path rather than a matter of framing.
5. **Nothing was committed.** The working tree already carried the Stage III
   round's uncommitted output when this round began.
6. **The case study was rewritten mid-round against a moving record.** Between
   the first and second readings of the deference ledger, an independent
   adversarial review overturned Stage III's positive reading: the comparator was
   found to contain no distinct future agent, `FUD_COMPARATOR_SPEC.md` v1 became
   a corrected defective record, and item 27 was filed. The worked example in
   `RESEARCH_STATE.md` had been written from the withdrawn reading and was
   replaced. It is kept as the worked case rather than swapped for a stabler one,
   because the aspiration survived intact while the constructed state shrank and
   the debt changed kind — which is the distinction the document exists to make.
   It is also the pass's only live test of the precedence rule: a lower-layer
   artifact refuted a consolidated reading, and the ruling landed in
   `DECISIONS.md` rather than as an edit to the round record.

## What this round does not establish

- No research claim, theorem, class, item status or definition changed. The
  case-study section restates the ledger and roadmap; where it appears to
  characterise the science it is quoting them, and they govern.
- The layer semantics are a **reading** of `AGENTS.md`, `DECISIONS.md` and
  `PROVENANCE.md`, not a legislation. That `DECISIONS.md` is the whole adoption
  mechanism is what those documents currently say; whether the maintainer wants
  it to remain the whole mechanism is itself a maintainer question.
- **The category error is asserted as available, not observed.** No agent is on
  record having read a `ci-only` canonical document as endorsed. The claim is
  that the documents permit it, which is checkable; that it has happened is not
  claimed.
- Whether the debt vocabulary reduces confusion is untested — no round has used
  it, and the honest test is whether the next consolidation reaches for it.
- **The line's compression debt is named, not discharged.** Recovering the live
  deference state still needs the roadmap, the ledger, the dispatch queue, the
  skeleton, the comparator spec and eight `DECISIONS.md` entries. Delta 6 is the
  cheapest available reduction and it was not performed.

## Outstanding maintainer actions

The queue is `DECISIONS.md`'s *Awaiting the author*; this is the round's own
record of what it reserved. Everything this round raised has been ruled on except
the two deltas above and one carried entry.

1. **Rule on the two remaining deltas.** Neither has a cost to waiting.
2. **Commit.** Every uncommitted file in the tree is now this round's — the
   deference rounds committed theirs at `bb8b351`. The move shows as a rename, so
   `git add -A` preserves it.
