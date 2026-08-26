# Decisions

Dated decision ledger. Settled decisions are recorded here and are not
re-litigated. What is still the maintainer's to decide is the queue below.

**Settled entries are append-only in substance.** Identifiers within them — a
renamed path, file, or namespace — are updated in place so the record keeps
resolving; anything else that changes lands as a new dated entry. This is what
*no negative ontologies* requires of a ledger that is also the one place history
is kept: a pointer that no longer resolves is not history, it is a dead link,
while a decision that turned out wrong is corrected by the entry that supersedes
it and not by editing the record of having made it.

**A new entry goes beneath the last entry sharing its date**, not at the head of
*Settled*. Newest-first still holds between dates; within a date the order is
arrival. This is a merge convention rather than a stylistic one: two rounds open
at once both wrote to the section head, and a resolution kept one side's text and
dropped the other's while every other file from that round landed. Appending
beneath a same-dated entry turns the collision into an ordinary append. The same
applies to `PROVENANCE.md`: new rows go at the end of the table they belong to.

## Awaiting the author

**The single queue.** Everything reserved to the maintainer, anywhere in the
repository, is listed here — a round that reserves something appends a line
rather than leaving it in its own report, per `AGENTS.md` §10. An entry leaves
when the decision lands as a dated entry below.

**An entry names what the decision turns on**, in one line: the taste, the idea
nobody has yet, or the external knowledge the round lacks and the maintainer has.
An entry without that line is a recommendation the round declined to adopt, and
is rejected at review — the round adopts it instead, as a dated entry marked
agent-decided and reversible.

**A merge is never an entry.** Merging is a fact about a pull request: a dispatch
either leaves auto-merge on or says on the pull request that the merge is the
maintainer's.

**A ruling taken in conversation is in force only once it is a dated entry
below.** The next round dispatched from that conversation lands it as its first
commit.

- **What the next research step is, given the inertness dichotomy.** The
  end-to-end slice establishes that the unconditional traderization theorem's
  admissibility hypothesis holds exactly for injunctions that change nothing, so
  every contentful injunction depends on a summable-liability condition nothing
  in the repository establishes — `PRIORITIES.md` item 61. The round recommends
  answering that before expanding the toy, and cannot say whether it is right.
  *Turns on:* external knowledge the round lacks — whether a paper, a
  collaborator, or the real-normative-practice term of the programme's benchmark
  needs the exact toy widened first. Both orders are defensible on the internal
  evidence.

- **Where the answerability layer's code lives.** The theory is authoritative in
  `projects/normativity/consolidation-aug9/` and the only implementation is in
  `projects/normativity/forward/`, whose own `FORWARD.md` says the tree may be
  deleted wholesale at any time. Three options, their costs, and the round that
  has already paid one of them: `PRIORITIES.md`, *Workspace friction*.
  *Turns on:* whether the program means to keep building on that layer.
  Promoting the code to a stable path earns its maintenance only if it will be
  imported again, and nothing in the repository says whether it will be.

- **Whether Q3 graduates, and what succeeds item 28.** Two candidate objects for
  what foreclosure loses — Cartesian frames with `Commit` and `External^{/}`
  separated by `image`, and the source corpus's family of sealed deliberations
  indexed by the day the advisor's channel is cut — fail on complementary axes,
  and nothing shows that no object supplying both exists. Read §§4, 7 and 9 of
  `projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md` and its
  red-team report. *Turns on:* whether the missing idea has arrived. A round can
  exhibit candidates and cannot say they are enough, which is the judgment
  *Where ingenuity is the bottleneck* exists to hold.

- **Whether returning `Unresolved` on every bare DR-MDP example is the shape
  this program wants.** The Carroll round's criterion licenses nothing on any of
  the five finite examples of the source it was dispatched against: with no
  enriched record, all five return `Unresolved`. That is either the correct
  result about what a DR-MDP omits — the round's own reading, and the reading its
  non-factorization witness supports — or a legitimacy layer that declines every
  case anyone actually asked about. Read
  `projects/normativity/legitimacy/rounds/2026-08-25-carroll-legitimacy-test/`
  `CRITERION.md` §6 and `README.md`'s verdict. *Turns on:* where the program is
  going — whether the next thing wanted is a criterion that decides bare cases,
  or an account of what a record must carry before any criterion can. The round
  is genuinely split and has no evidence either way.

- **Whether endpoint-preservation is a target this program wants.** The source
  corpus proposes that an advisor's influence is legitimate when it changes how
  fast the principal's deliberation converges and not where it converges to. It
  is conjecture-grade by its author's own declaration and is a claim about belief
  rather than authority, so it is a coherent adjacent target rather than a
  component of the current one. Read
  `projects/deference/note-dump-2026-08-11/notes/legitimacy-theory-v1.md` §§2,
  6–7 and §§2–4 of
  `projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md`.
  *Turns on:* where the program is going — this is *what is worth proving*, which
  no round decides.

- **Whether the deference kernel's grade acquires an index.** `GradeTrust` types
  the principal's grade as `C -> P -> Q` with no time, process or standing on it,
  so the legitimacy premise a cross-process deference theorem would consume has
  nowhere to attach. The change is one field — `W : A -> C -> P -> Q` — plus a
  stated hypothesis that the grade is a function of the authority in force, and
  it revises no registered statement, since `delegation_bridge` is proved for
  every `W`. Read
  `projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/CONSUMER_TEST.md`
  §§2 and 6. *Turns on:* whether the deference line is being restarted, and what
  a paper needs. It is a specification-layer edit in a paused line, and the round
  has no evidence about either.

## Settled

### 2026-08-25 — the legitimate state is replayed, not filtered

**agent-decided, reversible.** Re-rules the same day's frontier entry below,
which defined what is legitimately in force as the raw lifecycle intersected with
a derivability set.

A register in which a rogue authority — correctly refused — revokes a legitimate
norm decides it: the norm left the frontier because *something* in the raw
process removed it, and the persistence theorem reported no violation, because
its hypothesis was that no exercise acts on the object and one did. An attacker
with no legitimate authority could subtract from the enforcement target.

The legitimate state is now rebuilt from the recognized base by replaying the
proposed edits and applying the valid ones. A rejected edit is a no-op, so a
revocation nobody was entitled to make removes nothing.

*Rejected alternative:* the filtered frontier, which the round shipped and
tested.

*Record:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/COUNTERMODELS.md`
§1.

### 2026-08-25 — legitimacy is judged locally, not by outcome survival

**agent-decided, reversible.** Whether an exercise is legitimate is now: did
prior legitimate authority permit this exact edit, given this declared input and
this evidence of authentic exercise. It is not: does the edit survive removal of
the influence.

The case that decides it is ordinary persuasion. An agent with authority to
revise is argued into a revision; remove the argument and the revision does not
happen; challenge survival scores that as dependence. A legitimacy theory that
cannot let an agent be argued into a revision is not describing the learning this
programme exists to describe.

The cost is stated rather than absorbed: a counterfactual test can in principle
notice a dependence the record does not declare, and a declared-input test
cannot. The factorization hypothesis is what makes that safe, and it is falsified
by a record whose effect reads an uncited settlement.

*Rejected alternative:* challenge survival, which the two previous passes carried
as the central modal condition.

*Record:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/LEGITIMATE_EVOLUTION.md`
§7.

### 2026-08-25 — grounding an authority is not authorizing an exercise

**agent-decided, reversible.** A permit relation is a conjunct of validity. A
warrant granted cleanly, with impeccable provenance, used outside its domain,
issues nothing.

The previous formulation checked that an exercise's licence was recursively
derivable and never what the licence was for, so it established authority
provenance and not legitimacy of the particular exercise. `Permit` is a
parameter: the interface requires it be consulted and says nothing about what it
should say.

This exposes a gap in Reflective Integrity rather than in the interface — `PAuth`
carries a schema code and no domain — and the round names it instead of letting
the hypothesis look discharged.

*Rejected alternative:* leaving jurisdiction to the realization's `covers` field
without an abstract clause requiring it.

*Record:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/COUNTERMODELS.md`
§2.


### 2026-08-25 — legitimacy parents are not the objects an exercise acts on

**agent-decided, reversible.** Re-rules the same day's entry below, which took
all of an exercise's targets as its legitimacy parents on the evidence of a merge
register. A cleanup register decides the other half: a regulator revoking a
fraudulent warrant and granting a proper one acts on the fraudulent one and
inherits from its own charter, and a rule reading the objects acted on makes the
replacement illegitimate.

So the type splits. `affected(t)` is what the exercise acts on and constrains
nothing; `parents(t)` is what its issue inherits entitlement from and must be
derivable, all of it. The merge case is unchanged under the split, because there
the manufactured warrant really is a parent.

In the record calculus a cleanup is a revocation plus a separate creation, and the
creation inherits from its licence alone — so Reflective Integrity can express
both and needed no widening.

*Rejected alternative:* one relation for both, which is what the round's first
pass shipped.

*Record:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/COUNTERMODELS.md`
§2.

### 2026-08-25 — an exercise is individuated by what it does

**agent-decided, reversible.** A challenged replay may re-admit an event and have
it act differently. Whether that counts as the same exercise surviving is a choice
with consequences: under event identity the issuance-stability axiom needs the
record's schemas to be pre-state-blind, and under effect identity the
origin-necessity axiom needs it instead. The condition does not go away, so the
choice is made on semantics — an act that does something else is not the same act
— and the realization defaults to effect identity.

The prosecution is the reason this is recorded rather than assumed: the round's
first reading was that a finer identity would remove the hypothesis, and a record
whose effect changes in one component and not another shows it does not.

*Rejected alternative:* identifying an exercise with the event id, which is what
the first pass used and what makes `C28` a defect rather than a repair.

*Record:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/LEGITIMATE_EVOLUTION.md`
§8.1.

### 2026-08-25 — legitimacy does not mention liability

**agent-decided, reversible.** Entitled, answerable and sustainably enforceable
are three interfaces, and the succession frame carries no liability field. An
authority that inherits unbounded outstanding liability is still entitled and is
not serviceable, and folding the second into the first would make an insolvent
norm *illegitimate* and would make the abstract layer read a price.

The enforcement API already behaves this way: on exhaustion force is withheld and
"the endorsement keeps its normative standing".

*Rejected alternative:* a bounded-liability clause inside legitimate succession,
which would have made the enforcement consumer's missing theorem into a
legitimacy hypothesis instead of a consumer one.

*Record:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/TRADERIZATION_CONSUMER.md`
§5.


### 2026-08-25 — answerability continuity is not a conjunct of legitimate succession

**agent-decided, reversible.** A record in which an authority is transferred to
another principal under a licensed schema, and the episode the transfer ended is
never answered, satisfies every authority-side condition: the standing keeps its
identifier, its payload and its predecessors, because `applyEffect` is the
identity on a `Transfer`, and it is derivable against every challenge. Only the
holder moved, and only the account is outstanding.

Adding answerability continuity to the succession relation would refuse that
case, in which nothing about the authority is wrong. The account layer is
therefore separate data with its own two axioms, and a recognizing process that
wants an answerable counterparty reads it as a second condition rather than
getting it inside the first.

*Rejected alternative:* a single relation conjoining the two, which is what the
dispatch's §4 proposed as a candidate ingredient.

*Record:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/COUNTERMODELS.md`
§4.

### 2026-08-25 — derivability requires all of an exercise's sources

**agent-decided, reversible.** An exercise that supersedes several authorities at
once inherits from all of them, so the successor is certified only when every
source is. The alternative — one certified source suffices — admits a successor
of a manufactured authority and an earned one whenever the merging act itself
survives the challenge.

The decision could not be taken inside this repository's own architecture:
Reflective Integrity's `G6` refuses a supersession whose target is absent, so a
merge whose sources do not all survive is inadmissible anyway and the two rules
agree everywhere. A register of offices and appointments, which has no such
precondition, separates them and is what settled it.

*Rejected alternative:* existential inheritance, under which a lineage through
the clean half of a pair carries the pair.

*Record:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/COUNTERMODELS.md`
§5.


### 2026-08-25 — the enforcement charge is the safety layer's own quantity

**agent-decided, reversible.** The first pass of the end-to-end slice computed
`sum_omega max_j d_j(omega)` over the excluded worlds and called it the
exclusion depth, then applied the liability formula to it. That is neither
`LiveDeficitCertificate`'s sharp aggregate — `max_omega sum_j d_j(omega)` — nor
its conservative one, and it is not a quantity any theorem here mentions.

The slice now imports `enforcement`, `deduction`, `outflow` and `force_api` from
the traderized-enforcement round and calls them. It computes no liability
quantity of its own, and `test_safety.py` pins that the billed figure is the
certificate's and that it differs from the withdrawn one. *Rejected
alternative:* keeping a slice-local quantity under a distinct name, which would
have left two numbers a reader could confuse for the price of force.

The repair changed a conclusion, not only an implementation. The first pass
reported that a fixed injunction gets cheaper as the record settles. That holds
at a fixed day and fails across days, because the precision-`k` reading of a
value is `ceil(x*k)/k` and is not monotone in `k`; the counterexample is in
`src/trajectories.py` and the claim is withdrawn in the round's `README.md`.

### 2026-08-25 — the vertical slice's four local repairs

**agent-decided, reversible.** Taken by
`prompts/2026-08-25-end-to-end-vertical-slice/`, whose report states each with
its reason. Reversal is by re-ruling.

**The operative waist is `PForce`, not a new `PInjunction`.** The dispatch
proposed a new standing payload. Reflective Integrity already carries
`PForce (commitRef, schemaRef, compiledClause : Clause)`, `Clause` is already
opaque, and §35's `O_t` is already its projection; adding a second constructor
would have duplicated a payload and made the projection read two where it reads
one. *Rejected alternative:* `PInjunction` as specified, which would have been
honest to the dispatch and redundant in the record.

**The value waist is a new `PValue` payload constructor.** Licensed by
Meta-Stability's conservative-extension rule and free in practice, since
`delta`'s three clauses write a payload into a fresh standing state without
inspecting it. *Rejected alternative:* carrying a value specification as
`PCmt (NonStanceBearing, code)`, which would have forced a meta-level projection
to inspect object-level `content` and violated §3's stratification.

**The vertical-slice projection is `O_n = {(i, J_i)}`.** §35's projection is a
set of clauses; enforcement provenance and per-term conflict attribution both
need the standing identity, and two active standings with equal payloads
collapse in a set. No store, constructor or conservation law changes, so this is
a richer read of the same fold rather than a reopening. *Rejected alternative:*
carrying provenance inside the clause, which §5 of the dispatch prohibits and
which would have made the payload non-frozen.

**`sem_L` is a third parametric interpreter.** Alongside `[[.]]_S` and
`[[.]]_D`, keyed by settlement id, with rigidity, finiteness and computability
as its assumptions. *Rejected alternative:* a `content` field on `Settlement`,
which would have changed a record type in the frozen core's §33 signature to buy
the same thing.

### 2026-08-25 — a citation may be written in backticks where the name lint would otherwise refuse it

**agent-decided, reversible.** `tests/name_lint.py` cannot distinguish naming
the program after a person from citing a third party's published work, and a
maintainer of this repository is also an external author the normativity line
needs to cite. `projects/normativity/notes/PRIOR_ART.md` ships with the one
colliding surname in backticks, which the gate allows.

This is a workaround and is filed as friction rather than absorbed —
`PRIORITIES.md`, *Workspace friction*, F6. The fix is a matching rule exempting
a citation context; it changes a gate's logic, which is specification layer and
retroactive over every document the gate has already passed, so the round that
hit it did not take it. *Rejected alternative:* omitting the citation, which the
dispatch asked for and which would have made the note false by silence.

### 2026-08-24 — the reservation bar and epistemic debt

Two defects in the workspace's epistemic machinery, both in the rules rather than
in anyone's effort. *Awaiting the author* held thirty-seven entries against its
own "should normally be short", because `AGENTS.md` §10 governed how a reserved
item is *listed* and nothing governed what may be *reserved*; and the queue also
held decisions taken in conversation that never landed. Meanwhile epistemic debt
was accumulating in three shapes: free to pay and unpaid — kernel-checked
theorems unregistered, a handoff note describing a superseded theorem; untracked
— rounds consuming earlier `ci-only` results as hypotheses with nothing recording
the chain; and compounding — residual-blocker lists carried forward inside report
prose and growing round over round.

Ten rules, taken together. The rationale lives here and the rules live where a
reader would look for them.

**The reservation bar.** An entry enters the queue only when the round is
genuinely low-confidence in its own recommendation *and* can name what the
maintainer has that it lacks: taste, an idea nobody has yet, or external
knowledge — what a collaborator will accept, what a paper needs, where the
program is going. The entry says in one line what the decision turns on. An entry
that cannot say it is a recommendation the round declined to adopt. The retired
field is instructive: every rejected entry carried *cost of deciding now: low*,
which was true of all of them and therefore selected nothing. Cheapness is a
symptom, not a criterion.

**Recommend and adopt.** A round holding a recommendation lands it, marked
agent-decided and reversible, naming the rejected alternative. The asymmetry that
makes this safe is *no negative ontologies*: only the live entry survives a
re-ruling, so reversal costs the maintainer one entry and adoption costs nothing
if it is wrong. Deferring, by contrast, costs every later round the same
reconstruction.

**Merge is never a decision.** It is a fact about a pull request, and the
existing convention — auto-merge on unless a dispatch says otherwise — already
decides it. A merge in the queue is a queue entry that no reading can retire.

**Naming ships.** Rounds choose names, mark them provisional and list them. The
queue takes a naming item only when the name is about to propagate into Lean
identifiers or wiki vocabulary *and* the round genuinely cannot choose between
two candidates. Naming authority is not weakened; it is exercised as a periodic
batched **naming audit** instead of one entry per round, because a name-by-name
queue converts a single afternoon of judgment into thirty interruptions.

**Lean headlines register at merge.** A round shipping a Lean theorem it presents
as its result files the registry entry in the same pull request, and the merge is
the registration. "Whether X is worth registering" was never a decision: the
theorem is kernel-checked either way, and leaving it unregistered means the
repository holds a result it cannot say it holds. *What is worth proving* stays
reserved, and is exercised where it already was — in the priority items a
dispatch grants scope to file.

**Chat rulings land or are not in force.** A ruling made in conversation binds
nothing until it is a dated entry, and the next round dispatched from that
conversation lands it as its first commit. Two rulings had been in force in the
maintainer's head and nowhere else for a week, while the queue still carried the
questions they answered.

**`test-supported` is the ceiling for finite-model work.** A finite Python model
carries its round verdict and that class — or `witness-checked` or
`enumeration-verified` where the house harness actually adjudicates the instance
or generates the domain — and that is the class vocabulary working rather than a
defect for a bigger harness to repair. Growing the harness to raise a finite
model's class would move the judge inside the thing being judged. A finite result
becomes load-bearing by Lean port, and the dependency view below is how ports get
prioritized. New property forms stay permitted where a round needs one.

**Closed means a statement of record.** A component is **closed** only when a
Lean declaration or a checker invocation stands for it and its reopening
condition, where one exists, is a checkable event. Otherwise it is **open** or a
**living note**. "Closed provisionally" is retired: it reads as closed in every
summary and as open in every audit, which is the worst of both.

**Consumption is recorded.** Every round record carries `depends_on` — the rounds
whose results it takes as hypotheses, not the ones it cites — and the emitter
derives from it, per round, the transitive set of `ci-only` rounds that round
rests on. This makes the debt countable. It pays none of it.

**Contained friction is fixed by the round that hits it.** Non-retroactive, one
gate or one document, with its own null-input case: that fix belongs to the round
that hit it, recorded as agent-decided. Only friction whose fix would change a
spec-layer rule waits, and then it waits under the bar above. Reporting-without-
fixing was right when the concern was rounds redesigning the workspace around
themselves; the bar now catches that case directly, and the old rule was
converting ten-line repairs into permanent queue entries.

**What is not decided here.** Nothing about the research. The bar changes who
decides, not what is true, and every entry the triage below adopts remains
reversible by a later ruling.

### 2026-08-24 — the queue is triaged: the rulings the rounds recommended

Every adoption below is **agent-decided, reversible** under the bar above, taken
on the recommending round's own reasoning rather than on this round's independent
judgment of the mathematics. Each names what it rejects.

**The enforcement outflow account is market-owned.** The substrate grants the
privileged force channel one finite allowance, and `OutflowAccount.cap` carves
per-source budgets out of it for sources that want modular answerability. The
safety theorem needs only that the total be finite; a global account is what
`src/outflow.py` already implements, and it makes safety architectural rather
than contingent on who authored a constraint. *Rejected:* a source-owned account
per book, which makes the guarantee depend on every author's own budgeting.

**The outflow clause is a sibling of `P2`, under a stated shared principle.**
*Every privileged channel that can impose losses unavailable to ordinary bounded
participants carries a finite cumulative downside account* — of which `P2` and
traderized force are two instances with different bearers, holdings and means.
*Rejected:* broadening `P2`, whose declared means are refusal and bounded
participant budgets and from both of which the enforcement trader is exempt by
construction.

**At exhaustion the endorsement is quarantined and its deadline tolled.** Force
is withheld, the endorsement keeps its normative standing, and an answerability
deadline does not count a failure the substrate caused — which is the round's own
reading of what fits the existing architecture. Relaxation stays available as an
explicit request, because it buys a weaker promise than the source asked for.
*Rejected:* refusal at admission as the standing behaviour, which makes an
exhausted account an error rather than a state. Weakening the declared core
minimum was never an option: the worst deficit has no `θ` in it.

**The account is never replenished.** That is the option the safety theorem is
proved for, and it is the one an implementer is most likely to relax as an
obvious convenience — replenishment without limit is exactly the failure
`NL-SI-P1` names. A new constitutional era gets a new account with its own finite
allocation and its own bound, not a top-up of the old one. *Rejected:* bounded
global replenishment, and new-era allocation into the same account, both of which
leave a caller quoting a bound the account no longer has.

**`P1` names an obligation.** The settlement interface's enforcement clause
requires a declared conformance of whatever signs a force contract, rather than
certifying a core minimum of one named engine. The traderized-enforcement round
compiles the same condition out of `NL-SI-A2`'s admissible-reference polytope
into a trader, so two mechanisms now meet the clause and a clause naming one of
them cannot compare them. *Rejected:* the clause naming a mechanism. The frozen
consolidation is untouched either way.

**The two-channel architecture is adopted**: *what counts as admissible* and *how
finite prices are pushed toward admissibility* are separate, on the three
independent obstructions to collapsing them in that round's
`PAPER_RECONCILIATION.md`. Traderized force is a liftable module of one paper
rather than a separately consumable artifact, on theorem dependency. Coverage and
Liability keep their names, marked provisional, and go to the naming audit.
*Rejected:* one channel, and a separate force paper.

**`world-inclusive region` and `coverage(Due)` are not related.** Different
spaces, different quantifiers, and no map exhibited. A later round identifying
them must supply the map first. *Rejected:* leaving the question open, which is
how the two get silently identified.

**The reason state is `𝓡_n` and the normative record is `N_{≤n}`.** The wiki
writes the record as `Rₙ`; both senses are live, so the disambiguation is
required rather than optional. This round is scoped out of wiki content, so the
page edit is the next round to touch it. *Rejected:* keeping one letter for both,
which the dispatch that raised it flagged as a collision a later round would
resolve by identifying them.

**"admission" keeps the docket-intake sense.** It is the oldest use and the one
the objection grammar reads. The certificate verdict becomes **admissible edit**
and the state-indexed response set becomes **response class**, both provisional.
*Rejected:* giving the term to the certificate verdict, which would leave record
entry needing a new name in the frozen consolidation's own vocabulary.

**The reason-state interface is a living note, frozen provisionally**, at
`projects/normativity/legitimacy/rounds/2026-08-23-transition-certificates/REASON_STATE_INTERFACE.md`,
and so is the traderized force interface at
`projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md`. A research round may
leave a living specification behind. The freeze's reopening condition is the
round's own and is checkable: a concrete microhistory whose reason-dependency
structure cannot be expressed through contents, occurrences, record facts or
derived queries — the artifact, not an intuition. *Rejected:* holding an
interface in its round's memo until a second round consumes it, which makes the
second round's orientation pass the price of the first round's caution.

**The Stage V review surface is accepted as it stands.** Item 28's exact
static-view factorization theorem is the conditional representation boundary,
without unrestricted jurisdiction invisibility; item 7 is partially closed with
cross-process emission and calibration as its residue; Q3 stays ingenuity-level
model debt. All three are already how `PRIORITIES.md` marks them. *Rejected:*
adopting unrestricted jurisdiction invisibility, and marking item 7 completely
closed.

**The deck's path-gate entry stands.** `projects/normativity/deck-2026-08-10/**`
is a specification path, so a contributor pull request touching the maintainer's
own talk fails the gate. *Rejected:* reverting it, which makes the deck
contributor-editable — the state the intake was performed to avoid.

**Review status takes exactly two values.** The deck's row is
`maintainer-reviewed`, which follows from the maintainer having written it, and
the qualification — which frames are still model-drafted — moves to the notes
column where every other nuance lives. *Rejected:* a third, qualified value in a
two-valued field, which would make the label unreadable by anything that reads
labels.

**The source line's frontier question no longer has a referent.**
`CORRIGIBILITY_PAPER_LEDGER.md` was compressed from 471 lines to five by the
consolidation round of 2026-08-15; it now points at the wiki's Deference page for
the human account and at the state emission for what is registered, and has no
Movement I from which a pointer could hang. Removed as stale rather than decided.

**The per-commit `Model:` trailer is enforced**, in the form that changes no
rule: where a pull request's body declares a model, every non-merge commit it
adds carries a `Model:` trailer. A human-written pull request declaring no model
is asked for nothing new. *Rejected:* dropping the per-commit requirement and
keeping the pull-request body as the single record, which loses attribution on
every merge that is not a squash.

**The structured state holds a list of theorem-facing interfaces.**
`checkers/workspace_state.py` reads every `state/theorem_interface*.json`, so a
second interface is a new file rather than a trust-chain edit. *Rejected:* ruling
`theorem_interface.json` reserved for the response-learning theorem, which
documents the gap instead of closing it. The force interface's structured object
is not authored here; it stays a living note until a round consumes it.

**The `round/2026-08-17-lean-gate-scope` branch is landed rather than dropped.**
Its two commits carried `tests/lean_scope.py`, `tests/round_records.py`, the
generated views' move to `state/views/` and the ledger's append convention; all of
it passes the suite on current `main`, so the files are taken verbatim, their
self-tests re-run here, and both gates wired into `ci.yml` and `tests/run.py`. The
branch's own `PRIORITIES.md` renumbering is not taken, because two friction entries
were filed after it was cut and the list is renumbered here against the current
one. Its draft pull request is closed as landed, not as abandoned.

**Removed as already done:** merging PR #51, which merged at `3ebd33b`; merging
upstream `Formalized-Agent-Foundations` #2, which merged at `c0d885bf` and is the
commit `lean/lakefile.toml` now pins; and the Cartesian-frames repin, since that
pin is a commit on the upstream default branch carrying `CartesianFrames/`.
Deleting the mirror in `CartesianFrameBridge.lean` is now ordinary Lean work and
is filed as an item.

**Removed as not a decision:** reading `checkers/`. Maintainer reading is not a
queued item. `ci-only` is this repository's designed default, and its review
mechanism for a consumed result is a second executor's audit or a Lean port —
neither of which a queue entry can schedule. The harness stays honestly labelled
either way.

**Removed as registrations rather than decisions**, under the headline rule: the
traderized-enforcement inequalities, the projection results, the deductive
coherence region, and the max–min development. **Removed to the naming audit:**
the fourteen traderized-enforcement names, the assessment-process vocabulary, the
projection round's names, the deductive region's constructions, the
counterfactual-legitimacy vocabulary, and the transition-certificate vocabulary.
**Removed as filings:** the two formalization obligations the proof-closing pass
left — the erasure, discharged and registered; `DistanceComplete`, filed open —
and the counterfactual-legitimacy round's open questions.

### 2026-08-18 — the modified market's computability is discharged, via an additive upstream export

`ComputableMarket` is no longer a premise of the traderized-deduction chain, and the object
that replaced it is constructed rather than assumed. The blocker was module visibility:
`marketMakerSearchUpToTradeList_prim`, `tradingFirmTradesFromStageTradeLists_prim` and
`efAbsBound_prim` are `private` in the pinned dependency's `LIACompiler.lean`, and that file
carries 398 private declarations, so re-deriving them downstream would have meant
re-deriving the file.

The resolution is an upstream section that re-exports those ingredients publicly and changes
nothing else — no definition, statement or proof above it is touched, so nothing that built
before can break. The recurrence itself is deliberately *not* exported: a downstream
construction states and proves its own, which is where its soundness obligation belongs.

Statements of record: `Workspace.Normativity.Contrib.EnforcedCompiler.computableMarket`,
`.isLogicalInductor`, `.ProjectionSchedule.end_to_end_effective`. The one standing
hypothesis, `Primrec₂ E.trades` (`EffectiveEnforcerComputation`), is the definition of an
effective enforcer and sits where `DeductiveProcessComputation` sits upstream.

### 2026-08-18 — projection is the paper's traderization construction

Enforcement of a quantitative price region is by the **projection trader**, which holds
`λ_n(proj_{K_n}(P_n) − P_n)` on the day's fragment. The row construction is retained as
the simpler special case, as the comparison, and as the source of the
presentation-dependence observation; nothing about it is deleted or weakened, and for a
single halfspace the two are the same trader. `DistanceComplete` and the `d_∞` dual route
leave the critical path, because the paper's `ℓ^∞` conclusion follows from the Euclidean
one at the same tolerance.

Three consequences settled with it.

**The canonical intensity is calibrated, not merely bounded below.** The construction uses
`ρ_n = ε_n + A_n` and `λ_n = ρ_n/δ_n²` exactly, so the paper-facing budget carries no free
parameter and its day charge is `(ρ_n/δ_n)·d₂(W|_{Φ_n}, K_n)`. The identity
`λ_nδ_n = ρ_n/δ_n` holds only at that value; the general free-`λ` theorem is kept as a
supporting result.

**The cube-extension correction is accepted.** The market maker's day contract is applied
at a point of the region, which is not a world; that extension is justified by affineness
of a strategy's value together with the cube being the convex hull of the `{0,1}`
assignments on the traded support. The point actually fed to the contract is the fragment
target extended off the fragment by the displayed prices — a device for one inequality,
not a credence. The credal conclusion concerns the fragment projection only.

**The per-date-admission correction is accepted.** Zero risk capital follows from
admission by every region up to the horizon, not from world-inclusivity plus global
nesting; global nesting is a sufficient condition for it. The weakening to admission at
the final date is false, and there is a witness.

Statements of record: `Workspace.Normativity.Contrib.Projection{Force,Market,Compiler,
Budget,Calibrated,Enforcer}` and `Workspace.Normativity.Contrib.EnforcedComputation`.
Round: `projects/normativity/rounds/2026-08-18-projection-enforcement`.


### 2026-08-17 — five workspace-friction rulings

**The ledger takes new entries beneath the last same-dated one**, and
`PROVENANCE.md` takes new rows at the end of their table. Two rounds open at once
both wrote to the section head; a resolution kept one side and dropped the other,
and a pull request's two ledger entries and five provenance rows never reached
`main` while every other file it wrote did. The convention is in this file's
preamble.

**A round's report and its provenance row land together**, checked over what a
change adds rather than over what the repository contains: a change landing
`prompts/<round>/REPORT.md` must also carry a `PROVENANCE.md` row citing
`prompts/<round>/`. The whole-tree form was measured and rejected — most completed
rounds carry no such citation, because early rounds are covered by globs and the
per-round convention arrived later, and a check needing a thirty-entry allowlist
matches nothing.

**Generated views live beside the state they render from**, in `state/views/`.
They were kept inside a completed round's directory, so every round that indexed
itself edited an older round's folder to stay green — against the rule that a round
record is history.

**The feature-branch pin question is closed, and mirror-plus-cross-check is the
expected pattern** for upstream work in flight. The round that hit it mirrored the
fragment it needed and cross-checked every result by hand against the
authoritative definitions; the concrete case dissolved with the repin, and the
pattern is the answer rather than a workaround. No second exploratory pin is
added.

**The documented-command check and the root-document layer check are one entry**,
built alongside other work in that area rather than on their own. Both were
audited by hand on this date and are clean: no dead command pointer, required
contexts matching job names seven for seven, every root-level document in exactly
one layer. A gate with no failing case to try it against is not yet worth having.

Source: the maintainer's rulings on the friction list, taken in conversation
during the CI-scope round, and landed here by
`prompts/2026-08-24-reservation-bar-and-debt/` under the rule that a ruling made
in conversation is in force only once it is a dated entry.

### 2026-08-16 — Claude's wiki pull requests open under a token on the maintainer's account

`wiki/` is specification layer, so `path-gate` passes a pull request touching it
only when `GITHUB_ACTOR` is in `MAINTAINERS`, and the maintainer's AI collaborator
is who drafts those pull requests.

They are opened with a **fine-grained personal access token on the maintainer's own
account**: scoped to this repository alone, contents and pull-requests write and
nothing else, an expiry measured in days, minted per session, and never stored in
the repository, in its settings, or in any environment — which is *CI holds zero
secrets* applying to a human's credential as well as to a job's. That is the
existing attribution scheme extended to a new surface: the executing model is named
in the `Model:` trailers and in the pull-request body, so who pushed and what wrote
it stay separate facts.

**Squash auto-merge is off for a wiki pull request drafted on the chat surface.**
The register is prose a maintainer is the only judge of, and the gates check links,
pins and declared quantities rather than whether a page is right.

Rejected: adding an allowlisted machine account to `MAINTAINERS` and `CODEOWNERS`,
which is honest about who pushed and creates a second maintainer identity no human
is behind; and dropping `wiki/` from the specification list, which makes the
register contributor-editable and gives up what its own entry had just
established.

Source: the maintainer's ruling, taken in conversation on 2026-08-16, landed here
by `prompts/2026-08-24-reservation-bar-and-debt/`.

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
<!--historical-->`tests/check_frozen.py`<!--/historical--> and the
`frozen-integrity` job are retired.

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
