# Decisions

Dated decision ledger. Settled decisions are recorded here and are not
re-litigated. Anything awaiting the author is a stub in the section below, which
is the single queue: a round that reserves something appends a line there rather
than leaving it in its own report.

**Settled entries are append-only in substance.** Identifiers within them — a
renamed path, file, or namespace — are updated in place so the record keeps
resolving; anything else that changes lands as a new dated entry. This is what
*no negative ontologies* requires of a ledger that is also the one place history
is kept: a pointer that no longer resolves is not history, it is a dead link,
while a decision that turned out wrong is corrected by the entry that supersedes
it and not by editing the record of having made it.

## Awaiting the author

**The single queue.** Everything reserved to the maintainer, anywhere in the
repository, is listed here — a round that reserves something appends a line
rather than leaving it in its own report, per `AGENTS.md` §10. Each carries what
deciding it costs now, so it can be answered without reconstructing the context.
An entry leaves when the decision lands as a dated entry below.

**It should normally be short.** If it grows long, either rounds are reserving
what they could decide, or something structural is generating decisions and
belongs in `PRIORITIES.md` under *Workspace friction*.

- **Choose vocabulary for “admission.”** The normativity material uses the same
  family for at least three objects: the date a docket item enters the record,
  a certificate verdict permitting a lawful edit, and membership in a
  state-indexed admissible response set. *Doing it* is choosing which sense keeps
  “admission” and naming the others after reading
  `projects/normativity/rounds/2026-08-11-phi-regret-prep/PHI_REGRET_OBJECTIVE.md`,
  `src/certificates.py`, and the legitimacy bridge's `src/collapse.py`.
  *Waiting* leaves the wiki Glossary collision explicit and risks readers
  confusing record entry with normative certification.

- **Read `checkers/`.** Deferred once, deliberately, and kept here because
  deferring it does not make it go away: three files and three docstrings are the
  entire meaning of every Python claim this repository will make, and no
  maintainer has read them. *Doing it* is one sitting — the harness is stdlib-only
  and small on purpose, which is what makes it reviewable rather than what makes
  it right. *Waiting* costs nothing today and leaves every `witness-checked` and
  `enumeration-verified` claim resting on unread code. Nothing is blocked; the
  claims are honestly labelled either way.

- **Rule on the Stage V review surface.** Three linked candidate rulings:
  accept item 28's exact static-view factorization theorem as the conditional
  representation boundary, without adopting unrestricted jurisdiction invisibility;
  mark item 7 partially rather than completely closed, with cross-process
  emission/calibration as its residue; and retain Q3 as ingenuity-level model
  debt. *Doing it* requires reading the statements and §§2–9 of
  `projects/deference/notes/LI_NATIVE_DEFERENCE.md`. *Waiting* blocks no proof and
  leaves the current documents explicitly `ci-only` and unadopted.

- **Confirm the deck's path-gate entry.** `projects/normativity/deck-2026-08-10/**`
  was added to the specification enumeration in `tests/path_gate.py` by the
  φ-regret preparation round, so that a contributor pull request touching the
  author's own talk fails the gate. This is a trust-chain edit the round's
  dispatch did not scope, and it is flagged rather than assumed. *Doing it* is
  reading one line and one self-test case. *Waiting* leaves the entry in force;
  reverting it makes the deck contributor-editable, which is the state the intake
  was meant to avoid.

- **Rule on the deck's review status.** `PROVENANCE.md` now carries the first
  `maintainer-reviewed` research row in the normativity line, and it is qualified:
  the deck marks its own frames, 22 as the author's language and two as still
  model-drafted, so the row points at those marks rather than asserting a flat
  label. Confirm that the qualified review status is appropriate; it records
  review/provenance and does not adopt the deck's research content. *Waiting*
  costs nothing; the marks are on the slides either way.

- **Decide F4 — the answerability layer's code.** `PRIORITIES.md`, *Workspace
  friction*. The theory is in the authoritative consolidation and the only
  implementation is in a tree that declares itself deletable, so rounds building
  on it must adapt rather than import. Three options are stated there; *doing it*
  is choosing one. *Waiting* costs one reimplementation per round that touches the
  layer, and the φ-regret preparation round has already paid it once.

- **Rule on pinning the Cartesian Frames formalization.** `lean/lakefile.toml`
  pins Formalized-Agent-Foundations at `1fffea44`, which predates
  `CartesianFrames/`. That library was on an unmerged branch when the
  Cartesian-frames round was dispatched, so the round mirrored the fragment it
  needed and cross-checked every result against the authoritative definitions
  rather than take a trust-chain edit. **It reached `main` during the round**, at
  `e13dc5bd0117486b1947fbb5643045e14743e98d`, so the objection that made repinning
  unattractive is gone. *Doing it* is repinning to a `main` commit and deleting the
  mirror, which would put the cross-check's results inside the `lean` gate.
  *Waiting* costs the mirror's maintenance and nothing else — both Lean surfaces
  are green today.

- **Rule on graduating Q3, and on the successor to item 28.** `PRIORITIES.md` Q3
  asks how foreclosure is expressible and says what is missing is the object. The
  Cartesian-frames round supplies a candidate with a Lean witness — `Commit` with
  proper additive subagency for restriction, `External^{/}` with multiplicative
  subagency for transfer, separated by `image`. It is a candidate for **what is
  lost**, not for either hole Q3 names: no operation reassigns anything at a later
  index, and the interface is still one index deep. **A second candidate has since
  arrived from the line's source corpus** — a family of sealed deliberations indexed
  by the day the advisor's channel is cut, which supplies the time coordinate the
  frames could not and supplies no authorization relation at all. The two candidates
  therefore fail on complementary axes, and as each is currently formulated neither
  contains what the other supplies — though no combined object has been built and
  nothing shows none exists. That sharpens what graduation would require (temporal
  depth *and* authorization or capability structure, at once) rather than settling
  it; the ruling is still the maintainers'. Two linked rulings: whether
  that is enough for Q3 to graduate, and whether to file the round's proposed next
  target, restating the Stage-V factorization theorem over a signature carrying a
  frame and the choice actually taken in place of a `jurisdiction` field — which is
  a re-instantiation with a better inhabitation witness, not a new theorem. *Doing
  it* requires reading §§4, 7 and 9 of
  `projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md` and its red-team
  report. *Waiting* blocks the successor round and leaves item 28's answer resting
  on a worked case whose hidden payload no formula reads.

- **Rule on whether the source line's current frontier belongs in this line's
  ledger.** `CORRIGIBILITY_PAPER_LEDGER.md` records what *this repository* holds,
  and the corpus-reconciliation round declined to describe the source line's
  corrected faithful-acceleration results there on that ground — they are recorded
  only in the round's own reconciliation. The counter-case is that a reader of the
  ledger's Movement I now has no way to learn that the source line's own statement
  of that movement has moved on. *Doing it* is choosing between a one-line pointer
  from Movement I to the corrected statement, a described-but-unadopted subsection,
  and leaving it as it is. *Waiting* costs a reader of the ledger the knowledge that
  a fuller account exists one directory away; it blocks nothing.

- **Rule on whether endpoint-preservation is a target this program wants.** The
  source corpus proposes that an advisor's influence is legitimate when it changes
  how fast the principal's deliberation converges and not where it converges to.
  It is conjecture-grade by its author's own declaration, it is a claim about belief
  rather than authority, and this line's results say why certification can reach it
  even though certification cannot reach jurisdiction. So it is a coherent adjacent
  target rather than a component of the current one. *Doing it* is reading
  `projects/deference/note-dump-2026-08-11/notes/legitimacy-theory-v1.md` §§2, 6–7
  and §§2–4 of
  `projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md`,
  then saying whether this program pursues it, treats it as the source line's
  business, or holds it until the foreclosure object exists. **This is *what is
  worth proving*, which no round may decide.** *Waiting* costs nothing today and
  leaves Q3 carrying a candidate the program has not said it wants.

- **Decide the identity a wiki pull request is opened under.** `wiki/` is
  specification layer, so `path-gate` passes a pull request touching it only when
  `GITHUB_ACTOR` is in `MAINTAINERS`, and the maintainer's AI collaborator is who
  drafts those pull requests. Three options: open them with a token belonging to
  the maintainer's own account, with the executing model recorded in `Model:`
  trailers and the pull-request attribution block, which is the current scheme
  extended to a new surface; add an allowlisted machine account to `MAINTAINERS`
  and `CODEOWNERS`, which is honest about who pushed and creates a second
  maintainer identity that no human is behind; or drop `wiki/` from the
  specification list, which makes the register contributor-editable and gives up
  what the entry above just established. *Doing it* is choosing one. *Waiting*
  means a wiki pull request opened under any other identity fails the gate with
  nothing wrong with its content.

- **Decide the counterfactual-legitimacy vocabulary.** The round at
  `projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/`
  introduces reason-mediated non-capture, protected access, the licensed-reason
  trace, `ProtectedNormativeProjection` and its `identification` coordinate, the
  reason and residual channels, and the variation class — all marked provisional
  and listed in the round's report §9. *Doing it* is one sitting over
  `COUNTERFACTUAL_INTERFACE.md` and `MODEL.md`. *Waiting* costs little now and
  more once a second round builds on the terms.

- **Decide whether the counterfactual-legitimacy round's open questions become
  ledger items.** Five, in that round's `THEOREM_MAP.md` §6; the load-bearing one
  is whether a scorekeeping practice can produce a `Due` whose extension an
  advisor cannot select within, which is what the round's second clause needs and
  does not derive. The round filed none: it was not dispatched to file, and
  nothing in it enters the registry. *Doing it* is reading §6 and choosing which,
  if any, to file. *Waiting* leaves the questions recorded only inside a
  completed round.

- **Rule on whether the choice-channel coordinate is item 22's skeleton clause.**
  `PRIORITIES.md` item 22 asks for the weakest interface on which *prediction of
  authorization does not constitute authorization* is a theorem rather than a
  stipulation, and names the report coordinate as the candidate starting point.
  The round at
  `projects/deference/rounds/2026-08-18-principal-mediated-delegation/` builds it
  and answers the item's four questions: the report coordinate alone is not
  enough, a restriction on preparations is also required, the interface survives
  token responsiveness only when the efficacy clause is quantified over cells of
  the advisor's information, and the separation is explicitly not inferable from
  a run. *Doing it* is reading that round's `MODEL.md` §1 and
  `PRINCIPAL_MEDIATION.md` §§2–3 and saying whether the coordinate is adopted;
  adoption is a `FINITE_MODEL_SKELETON.md` version bump, so every track that
  consumed v2 would need rerunning or reconciling. *Waiting* blocks no proof and
  leaves item 22 answered in a round and unadopted.

- **Decide the principal-mediation vocabulary.** That round introduces `channel`,
  `mediates`, `residual`, cellwise efficacy, the acceleration class,
  `foreclosure_premium`, `eps_acc`, `eps_over` and `price_of_the_norm`, all
  marked provisional. *Doing it* is one sitting over `MODEL.md` and
  `REPAIR_LEMMA.md`. *Waiting* costs little now and more once a second round
  builds on the terms.

- **Decide whether two items are filed.** A two-index successor carrying
  `FINITE_MODEL_SKELETON.md` §4a's execution layer, which that round argues is
  the next investigation because foreclosure of a *later* correction is where the
  corrigibility target lives and is inexpressible at one index; and the
  price-weighted mixture repair of its `LI_PREDICTION_INTERFACE.md` §4, which is
  the only route found by which the prediction quantity the repair consumes could
  become one the pinned machinery is the right shape for. The round filed
  neither: it was not dispatched to file. *Doing it* is reading that round's
  report §6. *Waiting* leaves both recorded only inside a completed round.

## Settled

### 2026-08-16 — the wiki carries interpretation and philosophical gloss

The GitHub wiki is the maintainer-written home for interpretation, conceptual
synthesis, and philosophical gloss. The repository remains the verification
surface and lab.

Source: direct maintainer instruction during the PR #27 research-extraction pass.

### 2026-08-16 — volatile quantities in the wiki are declared, not detected

A number on a wiki page that changes when work lands is bound to machine state
by an HTML-comment marker, or wrapped `historical` when it records a past event
and cannot rot. `checkers/wiki_state_bindings.py` verifies every declaration
against `checkers/workspace_state.py --json` and fails four undeclared
high-risk forms: a pull-request number, and an integer immediately before
`claims`, `rounds`, or `priorit(y|ies)`.

**Detection is inverted.** The checker never decides which sentences are
volatile — the author declares, and the checker compares strings. A gate that
classified volatility in free prose would be guessing about English, and would
fail in the direction that grants passes: the sentence it cannot parse is the
one it lets through.

Aggregates are derived in the emitter, in a `counts` section seeded by demand —
a key exists there because a page binds it. Two alternatives are rejected.
**Template substitution**, generating values into the pages at sync time, makes
wiki source non-literal, complicates review of a pull request whose diff no
longer shows what a reader will see, and moves authority into the build;
checking keeps human-authored text primary. **Aggregate syntax in the marker
grammar** — `.length` or `.count` suffixes — moves derivation into the checker
and grows toward a query language the first time a filtered count is wanted.

Source: the maintainer-dispatched wiki state-bindings round, answering the item
the wiki-in-repo round filed.

### 2026-08-16 — write scope is enumerated and conditioned, not forbidden

`AGENTS.md`'s *Security* section stated one rule where the repository needs two.
What must be absolute is that **no credential is stored** — not in the
repository, its settings, or an environment. What a job's *run token* may do is a
separate question, and collapsing the two forbade every job that writes anything
while protecting nothing extra: the reason the section gives is that a verdict
must not be forgeable by what a contributor submits, and a job that fires only
after merge and publishes prose is not reachable by that.

Write scope is therefore permitted under four conditions, all four required:
`push` to a protected branch and never `pull_request`; publishing rather than
adjudicating, with no required check, registry, protected setting or claim class
downstream; the run token rather than a stored credential; and the grant written
on the job rather than as the workflow default. The jobs holding it are
enumerated in that section, and the enumeration is the protection — the same
shape as the specification list in `tests/path_gate.py`, and reviewable for the
same reason.

`wiki-sync` is the first such job. Nothing else in the repository holds write
scope, and merging stays with GitHub's auto-merge under branch protection.

`tests/workflow_scope.py` enforces it, in the `python` job: conditions 1, 3 and
4 over every workflow, both of the enumeration's failure directions, and
condition 2 in the one form a script can see — a write-granting job's context is
not a required check. That nothing consequential is downstream of what such a job
writes stays a review matter, and the section says so rather than implying the
gate reads intent.

Source: the maintainer's ruling during the wiki-in-repo and sync round, on the
conflict that round filed rather than absorbed.



### 2026-08-16 — the wiki's source is `wiki/`; the hosted wiki is a mirror

The pages of the human register live in `wiki/` and change through pull requests
that pass the gates. The hosted wiki is a build artifact: a merge to `main`
touching `wiki/` force-pushes the directory to `alignment-workspace.wiki.git` as
a single commit naming the source commit, and the job then re-clones the remote
and fails unless what it serves matches what was pushed. **Editing the hosted
wiki directly is unsupported and the edit will be overwritten without a record.**

`wiki/` is specification layer: it is enumerated in `tests/path_gate.py` and
owned in `CODEOWNERS`, so a contributor pull request touching it fails the gate.
Two files there are not pages and are not published — `ORIGIN.md`, the intake
receipt, and `CONVENTIONS.md`, which states what the register is for. The
exclusion is read from `checkers/wiki_links.py` by the sync job rather than
duplicated, so a file cannot be a link target the checker accepts and a page the
wiki does not have.

`checkers/wiki_links.py` requires every link between pages to resolve and every
link into this repository to carry a 40-hex commit SHA. It runs in the
`checkers` job, whose required-check identity is unchanged.

Source: the maintainer-dispatched wiki-in-repo and sync round.

### 2026-08-14 — required checks use stable infrastructural identities

The consolidation job's required context is `consolidation-verification`.
Project names and explanatory prose may appear in step names and logs, but not in
the external context branch protection matches. Renaming a research line must not
change the identity of its gate.

The workspace-state query distinguishes the sole modern claims registry from
the inherited Normativity consolidation. The latter remains a 180-claim legacy
foundation governed by its own ledger and status vocabulary; it is exposed as a
claim source and is not migrated or translated into modern epistemic classes.
Priority ownership and dispatchability are explicit metadata in `PRIORITIES.md`,
not consequences of item numbers.

Source: the maintainer-dispatched PR #32 reconciliation and machine-state
hardening pass.

### 2026-08-13 — the repository is the lab; the wiki is the human register

The repository holds experiment reports, priorities, contribution rules,
checkers, CI, specifications, and registries. Program interpretation,
architecture, vocabulary, and roadmap live in the GitHub wiki. The wiki is
maintainer-register content: contributors and dispatched agents neither read it
for instructions nor write it without a direct dispatch. The maintainer's
dispatch of the wikification round authorizes the wiki edits in that round.

Per-deliverable `FOR_HUMANS.md` files are removed after their usable content is
mined for the wiki; each affected round README points to the corresponding wiki
section. The agent-consolidated `consolidation-aug9/FOR_HUMANS.md` and
`INTERPRETATION.md` remain intact with a `superseded-by` pointer. That pointer is
the only edit to their content, made because a live epistemic pointer is permitted
for agent-consolidated records and prevents the frozen interpretation from
presenting as current.

The deference roadmap, prose vocabulary table, paper-arc ledger, and dispatch
queue are reduced to live pointers. Their exact specifications and statements of
record remain in the lab; interpretation and sequencing move to the wiki, while
registered state and filed priorities are queried from the repository's
structured state. This edits documents previously designated to govern the line
because that designation would otherwise make them competing living views.

Source: the maintainer-dispatched wikification and normativity round.

### 2026-08-13 — the project line is normativity

The project directory is `projects/normativity/` and its Lean namespace is
`Workspace.Normativity`. The word “leverage” names the technical measure or
operative-force quantity inside mathematical content; it is not the project
name. Completed round records, prompts, and consolidated internal text retain
the names true when written.

Source: the maintainer-dispatched wikification and normativity round.

### 2026-08-13 — legitimacy is a normativity subproject

`projects/normativity/legitimacy/` is the bridge between normativity and
deference. It owns the shared relational representation, write-separation
results, and the protection-versus-laundering tension. The relational
scorekeeping bridge round lives under its `rounds/` directory. Deference remains
a separate line and includes corrigibility.

Source: the maintainer-dispatched wikification and normativity round.

### 2026-08-13 — answerability, auditability, and efficacy are distinct names

**Answerability** is the relational status in which another participant with
standing attributes consequences under their practice and may raise a challenge
one owes an answer to. **Auditability** is the record property that every
liability has exactly one record-computable fate: discharged, mooted by
authorized revision, suspended, or open and charging. Loss of identity across a
retired vocabulary is an **audit discontinuity**. **Efficacy** is the
model-relative transition-system property that exercising a normative power
reaches its object under every policy of the other party.

Efficacy is named but not fully analyzed. Current mathematical support is limited
to the bridge fixture's C7 independence result and corrigibility theorems that
consume the grant invariant. Code identifiers and test names are deferred to a
later round.

Source: `projects/normativity/legitimacy/rounds/2026-08-13-relational-scorekeeping-bridge/TWO_ARC_INTERFACE.md`
§6; the maintainer's answerability-naming addendum to the wikification round.

### 2026-08-12 — the deference line's current source material is the 2026-08-11 tree

Taken by the corpus-reconciliation round under its dispatched write scope. A *which
document governs* ruling and nothing more: it adopts no content, registers nothing,
and moves no row to `workspace-established`.

`projects/deference/note-dump-2026-08-11/` is the line's **current source
material**. `projects/deference/note-dump-2026-06-27/` remains the line's **recorded
starting point**, is unmodified, and stays where the ported Lean's provenance
points, because the port was made from it and provenance records what happened.
Both trees stay specification layer.

The August tree's own intake receipt reserved this: it recorded that the deference
README and items 7–9 cite the June tree and that "whether and how they move to this
one is the maintainers' call, not this receipt's." A maintainer-dispatched round
whose dispatch asks for exactly that audit is that call. Pointers into the June tree
that name a document the August tree corrects have been repointed; pointers whose
target is unchanged have been repointed for currency, and the round's report records
which was which.

**What this does not settle.** Whether the source line's corrected
faithful-acceleration frontier should be described in this line's ledger at all is
in the queue above, unresolved. So is whether endpoint-preservation is a target this
program wants.

Source: `prompts/2026-08-12-corpus-reconciliation/REPORT.md`;
`projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md` §0, §6.

### 2026-08-11 — the governance report is removed, not relocated

Superseding the relocation decided earlier the same day. The report was moved under
`prompts/` as a round record; the maintainer's ruling is that it can go away, and it
has. Nothing of it survives, including the `PROMPT.md` recording that its dispatch
was never preserved.

**What it contained is elsewhere and current.** The checker meaning statements are
the docstrings in `checkers/` and the table in `checkers/README.md`; the resource
budgets and the permissive path-gate default were confirmed as decisions below; the
specification-path enumeration is `tests/path_gate.py`, which is the source of truth
and was never the report; and its four open questions were answered before it was
removed. It was a snapshot of a design that has since moved, kept at the root where
it read as current.

**One registered claim depended on it and was repointed first.**
`simplex.rational-points-sum-to-one` named the report as **both** its verification
and human register. Its documents are now `checkers/README.md` and
`CONTRIBUTING.md` — live, maintained surfaces rather than a dated snapshot, which is
what a claim's dual register should have been pointing at. **No claim changed class
and no statement of record moved**, and the registry gate still adjudicates it. This
is the second time a deletion at the root has come close to orphaning a registered
claim's documentation, the setup report being the first; the pattern is that
root-level reports get cited as registers because they are the only prose describing
the machinery.

**The round's attribution survives in `PROVENANCE.md`** and records that no round
record exists. That is a real loss of provenance, accepted deliberately: the
dispatch was already unrecoverable, so what was lost is a report whose content is
superseded, not a trail anyone can follow.

### 2026-08-11 — Stage IV: the future agent is still not in the model, and the reason is the signature

Taken at the close of Stage IV, after an independent adversarial review found a
conceptual collapse with no cheap repair. The round's positive reading is **withdrawn**.

**The later agent is still derived.** It was given its own credence so that it would
maximise its own expectation rather than the evaluator's. But its rule differs from the
evaluator's conditional argmax by exactly one argument, and remains a total function of
objects known at the earlier time. In the round's own headline instance the transferred
arm's realisation is *constant*, so the evaluator knows the realised action — the property
the round's gate existed to rule out. The check meant to catch that could not fail.

**Jurisdiction does no mathematical work.** Setting the principal's credence to the later
agent's, with the full-signal interface, makes the delegated arm **identical to the
transferred arm at every one of 32,805 instances tested**. The transferred arm is a
coordinate in the delegated arm's parameter space, and the jurisdiction assignment occurs
in no formula.

**The dominance result is the previous round's theorem with the arms swapped.** Stage III
put the evaluator's argmax on the transferred side and the transferred side trivially won;
Stage IV puts it on the delegated side and the delegated side trivially wins. Its scan is
padding: 19,468 of 26,244 instances contain no fallible later agent at all.

**The controlling finding, and the reason both rounds failed.** Two authorisation regimes
that induce the same realisation map are the **same object** in a signature whose only
outputs are such maps priced by one measure. This is a **type-level obstruction**, not a
modelling slip: a jurisdiction assignment is exactly what that signature cannot express,
and no additional parameter recovers it. The authorisation relation has to enter the type.

**Consequences.** No FUD proof round is to be dispatched, and **no further comparator round
of this shape**: two attempts have now failed at the same place from opposite directions.
The claimed-gate harness is deleted rather than repaired; `diagnose_collapse.py` replaces
it and every check in it records a defect. `FUTURE_AGENT_SPEC.md` is kept as a corrected,
collapsed record and is **not a binding input**. Three further round claims — the
advice-loss story, the interior requirement, and the fairness accounting — were checked and
are false or overstated, and are corrected in place.

**A repeated harness failure mode is recorded.** Stage III shipped four checks that could
not fail; Stage IV shipped ten, including a literal `True` and an `or True`. A mechanical
lint flagging any check whose condition is a constant or a type test would have caught both.

### 2026-08-11 — green merges itself, and the judge ships unread

The four questions carried over from the contribution-architecture round, answered.

**Auto-merge on full green.** A pull request whose required checks all pass merges
without a maintainer click. This is the architecture's own conclusion rather than a
convenience: the gates decide correctness, and if they do, a person in the path adds
delay and not a check. What review still decides — fit, naming, provenance
labelling, whether both registers are present, whether a result belongs in the
program — is judgment about work already merged, raised as an issue or a follow-up
like anything else.

Two existing gates make it safe rather than reckless, and neither was added for
this. A non-maintainer pull request touching a specification path **cannot go
green**, because `path-gate` fails it — so full green already means the change is
confined to the open layer. And `conservativity` fails anything adding an axiom,
changing specification shape, or altering the axiom output of an existing
declaration.

**It is GitHub's auto-merge, not a workflow, and that is forced.** A bot that merges
needs write scope, and *CI holds zero secrets, permanently* is a rule this ledger
does not get to spend on convenience. A merge performed by GitHub against the
required-check list grants this repository nothing.
`.github/apply-branch-protection.sh` now enables the setting and reads it back.

**Applied in the same sitting and verified by read-back**: seven required checks,
zero required approvals, code-owner reviews off, enforce-for-admins on,
force-pushes and deletion blocked, auto-merge on, and the check count agreeing
with the payload. The decision is live rather than recorded — which is the
distinction the settings-side rename failure exists to remind this ledger of.

**The checker harness ships unread, and the repository says so.** The maintainer
declined the reading pass, and that is recorded as a decision rather than an
omission: three files and three docstrings are the entire meaning of every Python
claim this repository will make, and no maintainer has read them. Nothing changes
in what is claimed — `witness-checked` and `enumeration-verified` already mean what
the harness does, and the harness is `ci-only` in `PROVENANCE.md` like everything
else. The entry stays in the queue because deferring it does not make it go away.

**The resource budgets are confirmed as proposed** — 200,000 enumeration points per
claim, 25 minutes of Lean build per pull request, no separate enumeration wall-time
cap. They are calibrated guesses against measured build times rather than derived
values, and a pull request needing more is a conversation and not an override.

**The permissive default for unlisted paths is confirmed and stays.** A path
matching neither layer is contributable, so a genuinely new kind of file does not
need a maintainer before anyone can work. The cost is that it fails silently in the
granting direction, which it just did — `RESEARCH_STATE.md` was contributor-editable
until someone noticed by hand. The answer is a check that every root-level document
classifies into exactly one layer, filed under *Workspace friction*, not a change of
default. **The enumeration itself is not re-approved**: it has changed several times
since it was proposed, and approving the version in that report would have approved
a list that no longer exists.

**A stale literal was found and fixed in the same pass.** The branch-protection
read-back required exactly eight checks; the payload has carried seven since
`frozen-integrity` was retired, so the script would have reported correct protection
as wrong. It now counts what the payload declares. A verifier with a hardcoded
expectation of the thing it verifies is a verifier that drifts, and this one drifted
in the direction that cries wolf rather than granting a pass — which is the harmless
direction, and still wrong.

### 2026-08-11 — the queue is cleared: six rulings

Taken in one sitting against the queue as the ethos pass had populated it.

**External citation: prose is not citable, and asking is the mechanism.**
Superseding the restatement in the entry below it, taken the same day. A
registered claim is citable externally carrying its epistemic class, which is what
the class is for. Prose is not — not the roadmaps, not the ledgers, not the round
reports — whatever label is attached to it. Anyone wanting to cite prose contacts
the maintainers.

The reason a label does not suffice: a citation can reproduce `ci-only` perfectly
and still rest on a reading the prose does not support, and the reader of the
paper cannot tell. Contact is the only point at which someone can say *that
passage does not mean what you are taking it to mean*. It is a message rather than
a review queue, cheap for the asker, and free when nobody asks — which is the
property the retired flagship rule lacked.

**`RESEARCH_STATE.md` is specification layer.** Added to `SPEC_PATHS` in
`tests/path_gate.py` with a self-test case. A trust-chain edit, recorded as one.
It matched no pattern, and an unlisted path defaults to the proof layer, so a
governance document was contributor-editable with the gate green. The failure
direction is safe: a specification pattern only ever removes write access.

**The governance report leaves the root.** It is a dated round record and was
sitting at the root among living documents, where it read as current: it still
named a retired CI job and carried its own competing *awaiting the author* list.
It was moved under `prompts/` as a round record, with its four undecided questions
carried into the queue above; the entry above supersedes that and removes it
entirely.

Two live pointers were repaired rather than left dangling, which is the same
failure the deleted setup report nearly caused. `projects/normativity/CLAIMS.md`
carried the file as **both dual-register documents** of the registered claim
`simplex.rational-points-sum-to-one`; both are repointed, and **no claim changed
class and no statement of record moved.** The identifier inside the settled
2026-08-11 root-cleanup entry is updated in place, per this ledger's header.
`GOVERNANCE_REPORT.md` is removed from the specification enumeration, which
`prompts/**` now covers.

**The deference line gets a terms table.** `projects/deference/notes/TERMS.md`,
recording current meaning and owning document for the vocabulary that has changed
under the mathematics — jurisdiction, the two competence vocabularies, the two
registers, conduct as proposal-plus-realization, and the status classes. It is a
**recording table and not a naming act**: every term stays provisional under
standard 6, and where it and an owning document disagree the owning document wins.
The line's canonical set is five documents rather than four.

**The leverage forward tree keeps its name.** `projects/normativity/forward/` is
confirmed. This was the cheapest moment to change it and it is not being changed.

**Further leverage frozen trees are registered at the next leverage round**, not
now. The accepted risk is stated rather than implied: material may drift on the
maintainer's machine before it is frozen, in which case what gets registered is a
later version than the one the current work was done against.

### 2026-08-11 — maintainer attention is a design parameter, not a backlog

Three rulings, taken together because they follow from one fact: the maintainer
writes in few places and does not read most of what this repository produces.
That is throughput, not neglect, and the constitution was written assuming
otherwise in three places.

**The flagship rule is retired.** "Headline or flagship documents may not remain
`ci-only`" is gone from `AGENTS.md` and `PROVENANCE.md`. It named a state that
nothing in the process could reach, and an unreachable requirement is worse than
an honest label — it makes the label look provisional when it is in fact the
standing condition. `ci-only` is now stated as what almost everything here is,
including the documents a reader meets first, and `maintainer-reviewed` as a rare
deliberate mark rather than a state material eventually reaches.

**External citation is restated to stand on its own.** It previously routed
through the flagship rule and so retired with it. What replaces it is weaker and
attainable: anything cited externally carries the status it actually has — a
registered claim its epistemic class, unreviewed prose as unreviewed. The failure
it guards against is a citation silently upgrading `ci-only` prose into an
assertion of record, which is something the citer does and the repository cannot
gate. Whether that suffices for the maintainer's own citations is the one
residual question, and it is in the queue above.

**A maintainer-dispatched round may file `PRIORITIES.md` items within its own
scope**, with its `PROMPT.md` as the authorization record and the filing named in
its report. Demand-gating is kept: nothing enters the registry except in answer
to a filed item, and contributors still do not file. What changes is that the
maintainer act is one approval of a wave rather than one retyping per item — the
demand structure is what a stranger's pull request must not set, not something
that must pass through a person's hands twice.

**Naming is deliberately not relaxed with it.** A round proposes provisional
names and marks them; what a thing is finally called stays reserved. A name that
ships is very hard to change, and nothing about throughput makes that less true —
the two acts looked alike in the friction report and are not alike.

**One queue.** `AGENTS.md` §10 now requires a round that reserves something to
append it to *Awaiting the author* above, rather than leaving it in its own
report. Four sources of reserved items existed and none was the answer to "what
needs me?"; the ledger's own section was the closest and was not being fed. The
section is populated as of this entry and should normally be short.

### 2026-08-11 — Stage III did not build a FUD comparator, and says so

Taken at the close of Stage III, after an independent adversarial review overturned the
round's own first-draft conclusions. The round's positive reading is **withdrawn**.

**The constructed transferred arm contains no future agent.** Its selection was defined as
the argmax of the *evaluating agent's own objective under the evaluating agent's own
credence*, which that agent can compute at the earlier time. So the arm confers no
cognition the evaluator lacks, and no object representing a distinct future agent occurs
anywhere in the model. What was compared is the principal's contingent plan against the
**optimal later-measurable plan** — the envelope that the previous phase priced and
recorded as explicitly *not* the fully-updated comparator. Skeleton v2 §4 declared that
comparator a hole and warned that careless invention is how it collapses; the round
invented carelessly in the way it had been warned against.

**Three consequences, all recorded rather than repaired by assumption.** The dominance
result carries no fairness hypothesis and is `∑ maxima ≥ ∑ anything`; its original
docstring described a statement that did not exist. Its real driver is future-agent
**infallibility**, not "epistemic improvement only" — a witness with every fairness
condition intact, in which a better-informed but fallible future agent makes the gap
strictly negative, is now carried. And the observation that no jurisdictional term appears
in the arithmetic was guaranteed by construction: the specification waived the null effect
and the whole execution layer, which the previous phase recorded as the place all of
protection's valuation content sits.

**Verdict: not well-posed as constructed.** No claim is made that fully updated deference
is false, or that jurisdiction has low value; both were outside what the model could see.
**A FUD proof round is not to be dispatched.** A successor needs two things, and they are
the same two prerequisites the previous phase already named: a future agent with
independent existence, so that *better-informed* and *correct* can come apart; and the
execution layer reinstated with a declared null quantity, so that a jurisdiction
assignment is something a valuation can price rather than a label on a selection.

**What survives.** Fifteen kernel-checked theorems, renamed to `EnvelopeDominance` to match
what they prove and reusable by any successor. The fairness apparatus and three confound
witnesses, each now moving exactly one variable. The reduction: the gap *is* the delegation
deficit against the later-measurable comparator class, so the credence collapse applies to
the same object rather than by analogy, and any credence-free hypothesis bounding it is it.
And the confirmation that **underwriting is absent from the engine**.

**A repeated classification error is recorded.** The round's competence slot was labelled
as the previous phase's credence-free hypothesis; it compares grades to a conditional
expectation, so the credence occurs in it and it is a joint competence–credence hypothesis
under skeleton v2 §2a. This is the same error the competence track caught for grade trust,
made again. A mechanical check — does the hypothesis mention the credence? — would catch
both.

**The specification is kept, corrected, as a defective record** rather than withdrawn: its
fairness apparatus is reusable and the defect is the round's main finding. It is marked as
**not a binding input** to any proof attempt.

### 2026-08-11 — the setup and scrub reports are removed from the root

Maintainer instruction, taken during the Stage III round. Both were
round-contemporaneous records that had outlived the root: the setup report
described a toolchain and CI configuration now readable from the pinned files
themselves, and the scrub report recorded the judgment calls of two scrub rounds
whose own round records under `prompts/` survive.

Four live pointers were repaired rather than left dangling, because a pointer that
no longer resolves is a dead link and not history.

- `tests/path_gate.py` listed the setup report as a specification path. Removed from
  the enumeration. This is a **trust-chain file** and the edit is recorded here for
  that reason; the entry it removes named a file that no longer exists, so the gate
  is not weakened.
- The contribution-architecture report's specification-path listing is brought back into agreement
  with the gate. The two must agree, and the gate is the source of truth.
- `projects/normativity/CLAIMS.md` carried the setup report as the **verification
  register of two registered `lean-proved` smoke claims** (`smoke.faf-asymp-refl`
  and `smoke.chain-compiles`, both answering item 13). Deleting it would have left
  two registered claims without half their required dual register, so both doc
  pointers are repointed to `prompts/2026-08-10-repo-scaffolding/REPORT.md`, the
  surviving round record that documents the same setup verification. **No claim
  changed class and no statement of record moved.**
- `PROVENANCE.md`'s row for the file is dropped; `PRIORITIES.md` item 10's context
  pointer now names the round record.

Two references are deliberately **not** repaired. `AGENTS.md`'s chat-dump section
requires a collator to produce a `SCRUB_REPORT.md` alongside a bundle; that is a
standing requirement on future dumps, not a pointer to the deleted file, and it
stays as written. And `projects/deference/note-dump-2026-06-27/ORIGIN.md` names the
root scrub report in its intake receipt; that tree is `agent-consolidated` and its
receipt records what was true at intake, so it is not rewritten.

References under `prompts/` are round records and keep what was true when they were
written.

### 2026-08-11 — skeleton v2 is installed; jurisdiction replaces authority in the canonical roadmap

Taken at the Stage II closure pass, after Tracks H, I, K, L and M returned and were
independently re-verified at `8c71ef9` (1843 build jobs, 142 axiom results across 10
files, full suite green, Track L's harness reproducing all of its 71 checks, 1,574,640
models and 1,443 refutations exactly).

**The `FINITE_MODEL_SKELETON` execution clause is ruled on and installed as v2.** Track
K's proposed §9.2 clause is adopted: reports, an authorization relation, a null effect,
an execution map, and a derived per-report authorized menu. It is required because v1
carries no capability structure, so fail-closed in its strong form — the agent *cannot
execute* an unauthorized alternative — is not expressible in v1 at all. The patch is
conservative: at the free instantiation every v1 statement is a v2 statement.

**The quantity is indexed over interventions plus the null effect.** Required, and for a
sharper reason than "protection needs a cost for refusal": under any protecting menu some
conduct realizes the null effect, so without the extension the valuation is not a total
function and every V-register statement over the execution layer is *ill-typed* rather
than false. Its value is a declared per-instantiation modelling commitment with no
default, because all of protection's valuation content sits in it and the sign of the
result depends on the choice.

**Correction to the closure dispatch.** That dispatch identified this amendment as
required for the certificate's grade-register theorem to be a theorem over the skeleton.
The amendment is required, but not for that: the grade-register theorem mentions no
quantity at all, and is untouched. The real gap in its neighbourhood is that the
amendment extends the quantity to the null effect while **nothing extends the principal's
grades to it**, so the two registers have different domains. v2 therefore declares that
the V-register scores *realizations* and the grade register scores *proposals*; a
grade-register statement read over realizations is ill-typed, not false. Extending the
grade register to the null effect is left open, because supplying it is a theory of what
the principal's judgment says about refusal and no track has proposed one.

**No promoted result is invalidated.** Everything the certificate rerun refuted or
reinterpreted sits in the set the Lean promotion deliberately declined to port as resting
on the uniform grade-to-quantity relation. The exclusion absorbed the entire impact, and
the justification that arrived is stronger than the one given at the time.

**Competence vocabulary is adopted; cross-decision aggregation is declined.** A
competence hypothesis is a predicate of the principal/world pair alone; anything also
mentioning the agent's credence is a joint competence–credence hypothesis and is declared
as one. The cross-decision patch is declined on the competence track's own evidence: no
aggregate condition constrains any named decision, so the patch buys nothing the finite
kernel needs.

**Terminology: jurisdiction.** The canonical roadmap now says *jurisdiction* — protected
control over which process's authorization is constitutively required for an intervention
to become executable. It is operational and capability-based: not moral legitimacy, not
objective correctness, not preference alignment, not behavioural agreement, not epistemic
superiority. No `HasRight` predicate is introduced and no token or cryptographic
implementation is canonized. Historical records keep the word "authority" as written;
this is a change of current terminology, not a retroactive rewrite.

**The certificate governs the complement, not the surround.** "Categorical authority plus
quantitative autonomy *around* it" is replaced by "categorical principal jurisdiction plus
quantitative AI autonomy on the complement where that jurisdiction is waived". Forced by
an exhaustive result: inside a live protected interface every authorized option other
than the report's own designation is an override, so there is no third kind of option for
a certificate to license. And certification cannot converge to jurisdiction — the whole
valuation difference between the protected and unprotected architectures is bounded by
the certificate's own bound, attained, so tightening it shrinks the distinction at the
same rate and never reveals it.

**Override-protection is bought; liveness is conceded.** Categorical protection against
override and categorical liveness against obstruction cannot both hold while the agent
retains any discretion. Fail-closed as written buys the first. Making refusal expensive is
preference-relative and reintroduces underwriting, so a residual refusal mechanism may not
become the conceptual explanation of corrigibility.

**Correction to a verified Phase I record.** The certificate round's Theorem C(b) glosses
its override bound as a strict-minority claim; it is not, with an exact counterexample at
override mass three fifths of the certified credence. What the support-floor clause
delivers is only that the certified act executes on positive mass. Recorded here rather
than edited into that round's report, which is history under *no negative ontologies*.
Source: `prompts/2026-08-11-phase-ii-certificate/REPORT.md` §4.

### 2026-08-11 — choice-level competence is retired; the certificate gates on self-assessed error

Two decisions taken after Phase II's competence and prediction tracks returned and
were verified.

**Competence may not be stated as a regret bound.** Pointwise, average and
selector-relative decision-regret assumptions are each *equivalent* to the
delegation inequality they were meant to buy, not merely sufficient for it. The
mechanism: decision regret is nonnegative, so there is no cancellation, and the
supremum of the delegation deficit over credences is the maximum regret — making
the weakest credence-free hypothesis implying the target uniformly **be** the
target. Asking for the weakest assumption preserving the theorem is therefore
ill-posed.

The candidates are retired as a **statement shape**, not merely as parameter
choices. They may not be rescued by tuning constants, nor by trading the pointwise
form for a Cesàro or selector-relative one — the averaged forms fail worse, being
invariant under changing finitely many decisions and so constraining no named
decision at all.

The equivalence depends on point masses being admissible credences, and that
dependence is recorded rather than exploited: **the admissible credence class is
not restricted away from point masses to evade the result.** Such a restriction
would need independent motivation, and the fully-updated-deference theorem is meant
to stay meaningful precisely as the agent becomes highly informed.

Competence moves into a richer vocabulary — cardinal grade structure rather than
which option was chosen — because a hypothesis in the conclusion's own vocabulary
can only be the conclusion. The strongest non-circular candidate found,
decisiveness-gated calibration, is preserved together with its unbounded
near-indifference leakage term, and is **not** canonized pending the Phase II
synthesis.

**The certificate engine gates rather than eliminates.** Magnitude prediction error
cannot be forced to zero: a trader's net worth is affine in the settlement vector
and absolute value is not, so no instrument reaches it. Rather than assume the
principal is approximately predictable, the certificate is reoriented onto the
selective validity of low-error self-assessment — the agent prices a contract
settling to its own error statistic, and the guarantee sought is that this claim is
statistically trustworthy on the class where it licenses autonomous discretion. The
criterion need not make the principal predictable; it should make the agent's claim
that its prediction error is low trustworthy where that claim does work.
Measurement and gating, not error elimination.

An explicit principal-predictability assumption is retained only as a baseline
corollary, never as the conceptual engine. The agent's self-measured indecision,
which Phase II's exact squared-error decomposition supplies directly from its own
prices, is retained as the canonical special case and the likeliest first Lean
theorem.

### 2026-08-11 — the deference line's canonical documents, and `notes/` as specification space

Four documents are canonical for the deference line:
`projects/deference/notes/CORRIGIBILITY_ROADMAP.md` for current architecture and
execution planning, `CORRIGIBILITY_PAPER_LEDGER.md` for human-readable research
status, `DISPATCH_QUEUE.md` for what is dispatched and what may not yet be, and
`FINITE_MODEL_SKELETON.md` for the frozen finite specification object a round's
finite tracks bind to. Precedence: where roadmap and ledger disagree about whether
something is established, the ledger wins; where prose and the claims registry
disagree about what is established in this repository, the registry wins.

The decision was made by the maintainer before the round was dispatched, and the
round implemented it. It closes the stub that asked which deference documents are
canonical — the answer is these four, at these paths, and the line no longer has to
be given its inputs in a dispatch.

**A gate correction went with it, and it is the part worth recording.** The round
was authorized to create the four documents and found it could not honestly do so:
`tests/path_gate.py` classifies with `fnmatch`, whose `*` crosses a path separator,
so the enumeration protected `projects/*/README.md`, `CLAIMS.md`, `MODEL.md` and
`THEOREMS.md` **by basename at any depth** — and nothing else under a line's
`notes/`. A canonical document was therefore specification layer or not according to
what it was called: `notes/README.md` was protected, `notes/ROADMAP.md` was in
neither layer. The intended policy is that a line's `notes/` is maintainer working
space, so `"projects/*/notes/**"` was added to the specification enumeration with
three self-test cases, including the regression case that an arbitrary filename
under a line's `notes/` classifies as specification. A contribution surface nested
under `notes/` still resolves to the proof layer, because proof patterns win.

This is a trust-chain change and was separately authorized as one. The failure
direction is safe: adding a specification pattern only ever removes contributor
write access and cannot grant a pass.

**A second candidate correction was authorized conditionally and not made.** The
same authorization covered `projects/*/FOR_HUMANS.md` *if* inspection confirmed
`AGENTS.md` designates it a specification-side artifact. Inspection does not confirm
it. `AGENTS.md` names `FOR_HUMANS.md` as the human-register *style* and, in the same
document, assigns "dual-register documentation of contributed results" to the
**proof** layer — while also requiring every substantive deliverable to ship both
registers. Protecting the path would forbid a contributor from writing a register
they are required to ship. The existing `projects/*/THEOREMS.md` protection has the
same defect, and `projects/*/VERIFICATION.md` — named beside `THEOREMS.md` in the
dual-register section — is not protected at all. The three are one question about
where dual-register documentation lives, and it is left open rather than half-answered.

### 2026-08-11 — `frozen/` retired; received work becomes line content

The four frozen trees move into the research lines they belong to and become
`agent-consolidated`: ordinary content whose norm is that it is not tweaked.
`tests/check_frozen.py` and the `frozen-integrity` job are retired.

**The trade, so it is visible rather than implicit.** The freeze bought three
things: a stable citable path, a record of what each tree was when received, and
protection against an agent quietly rewriting the corpus. Only the third needed a
wall — the first two need a receipt, which is what each tree's `ORIGIN.md` now
is. What the wall cost was that every legitimate change, including both scrub
rounds, had to go through a manifest procedure, and material that is the
*starting point* of ongoing work was structurally forbidden from being worked on.
The failure the wall aimed at is one that the path gate, review, and git history
already make visible. Keep the receipts; drop the wall.

The move changed no bytes: all four trees recomputed to their intake digests
after `git mv`. The consolidation's self-verification job stays, retargeted and
renamed `consolidation-verification` — it is the piece of the apparatus that
carried real information, since it says whether the results still verify in a
current environment.

### 2026-08-11 — the ledger is append-only in substance

Settled entries are not edited except to keep their identifiers resolving. The
rename round updated a settled entry in place, which *no negative ontologies*
required and which the header did not authorise, so the ledger was neither
append-only nor freely editable and the round's report recorded both readings
without choosing. The header now states the rule; the wording is in the header
rather than here so it is read before the entries are.

One case it does not cover, recorded rather than legislated: removing something
from a settled entry for privacy — a name, a personal detail — is neither an
identifier update nor a thing a later entry can fix by appending. It has not
arisen; this ledger is deliberately exempt from the name lint. If it does arise,
the header needs a third clause rather than an improvisation.

### 2026-08-11 — every gate ships a case proving it fails on nothing

Two gates have reported green while checking nothing — the DCO gate counting a
synthetic merge commit, the attribution gate accepting the pristine template.
Both were caught by hand, which is not a mechanism. Each of the nine gates now
carries a `--self-test` run in the same CI job as the gate, and four had real
null-input holes closed in the same change: the path gate and the DCO gate
passed on an empty file list inside a pull request, conservativity re-baselined
itself when its shape file was missing, and the frozen check verified an empty
registry. A gate that matches nothing is indistinguishable from a gate that
works, and it fails in the direction that grants passes.

### 2026-08-11 — the contribution funnel is `PRIORITIES.md`

Renamed from the file that held it, and reframed with it. The document says what
the program wants done next, in the maintainer's order — not an inventory of
everything unsolved. An item's absence means nobody has asked for it. Difficulty
tags are unchanged, and the frozen consolidation's own list keeps its name, since
frozen trees are not renamed.

Three code paths read the file — `checkers/registry.py`, `checkers/run.py`,
`tests/path_gate.py`. The registry's lookup had the failure mode the rename was
most likely to trigger: a missing file produced an empty item set and every
`answers_item` check then skipped itself while the gate stayed green. It is now a
hard failure, and both cases are permanent self-test cases.

### 2026-08-11 — slop discipline is a standard, and grounds for rejection

Padding is a correctness problem in a verification repository, not a matter of
taste: a reader who cannot tell which sentences carry content cannot audit, a
document that restates itself hides its errors in the restatements, and volume
inflates the cost of the maintainer review the architecture rests on. The rule is
in `AGENTS.md`, summarized in `CONTRIBUTING.md`. Agent reports are deliverables
under it. **A pull request whose content is correct and whose prose is padded may
be rejected on that ground**, said plainly rather than merged and cleaned up
after.

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
**`Workspace`**, so that the two agree: namespaces are `Workspace.Normativity.*`
and `Workspace.Deference.*`, the library root is `lean/Workspace.lean`, and the
Lake package is `workspace`. This closes the naming stub the scaffolding round
opened, and closes it at the cheapest moment — before any real development lands
in the library.

The leverage forward tree is **`projects/normativity/forward/`**, with
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
