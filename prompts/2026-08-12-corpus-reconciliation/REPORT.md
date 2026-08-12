# Report — corpus reconciliation

**Prompt author:** GPT-5.6 Sol (OpenAI). **Executor:** Claude Opus 5 (Anthropic).
**Dispatched and executed:** 2026-08-12. Write scope granted by the dispatch, §E.

Deliverables: `projects/deference/rounds/2026-08-12-corpus-reconciliation/` —
`RECONCILIATION.md` (verification register), `FOR_HUMANS.md` (human register).

## Deviations from the prompt

Two, both factual corrections the dispatch's §8 requires be stated rather than
absorbed.

**1. The corpus was not present in the working clone.** The dispatch states the
repository "has just ingested" the tree. It had — as commit `4ff5048` on
`origin/main`, pushed while the clone was on a feature branch two commits behind.
The tree existed on no local or remote ref visible before a fetch. The round fetched
and branched from `origin/main`, which also carries the Cartesian-frames round
(`1585735`) that the local branch held only in unmerged form. **A round dispatched
against a just-merged intake should fetch before concluding anything about what the
repository contains**, and this one nearly filed a finding that the corpus was
missing.

**2. The attribution correction has no workspace surface to reach.** The dispatch
directs that "no workspace document perpetuates the old attribution." No workspace
document carries it: `grep -rn "Eisenstat"` over the repository outside the two
source trees returns nothing, and no canonical surface names the conjecture or
repeats a verdict resting on it. The instruction is discharged by verification
rather than by edit, and the verification is the deliverable. `RECONCILIATION.md`
§1.4 records why the exposure was structurally unlikely rather than lucky.

One further correction to the dispatch's framing, which changed the work rather than
a fact. The dispatch's §"What changed" asks what the faithful-acceleration
adjudication does to items 7–9. The answer is **nothing**, and establishing that
took the round's single most useful mechanical step: the statement-level audit those
items quote is byte-identical in the June and August trees. The dispatch's premise —
that a superseding corpus puts its predecessor's audit findings in question — is
reasonable and turned out false, and it is worth recording that it was checked by
`diff` rather than by reading.

## Files read

**Source corpus, `projects/deference/note-dump-2026-08-11/`.** `ORIGIN.md`;
`README.md`; `wiki/index.md`, `conventions-and-status-labels.md`,
`new-chats-2026-07.md`, `eisenstat-conjecture-attribution.md`,
`epistemic-discipline.md`, `faithful-acceleration-result.md`,
`delay-and-visibility.md`, `open-problems.md`, `mart-implies-value.md`,
`value-iff-mart.md`, `total-trust-implies-value.md`, `soft-self-endorsement.md`;
`lean-deference/AUDIT.md` and its module list;
`notes/legitimacy-theory-v1.md`; `varying-question-lab/theorem-ss-streamlined.md`,
`varying-question-synthesis.md`;
`deference-trust-lab/run3/work/trace-nonrecoverability/` (both registers and the
Lean declaration list). Directory listings of the full 227-file tree.

**June tree.** `lean/AUDIT.md` (diffed against the August copy),
`lean/LeanDeference.lean` (the declarations the workspace ported), file listing.

**Workspace.** `AGENTS.md`; `PRIORITIES.md`; `DECISIONS.md`; `RESEARCH_STATE.md`;
`PROVENANCE.md`; `projects/deference/README.md`; `notes/CORRIGIBILITY_PAPER_LEDGER.md`,
`CORRIGIBILITY_ROADMAP.md`, `DISPATCH_QUEUE.md`,
`CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md`;
`lean/Workspace/Deference/Contrib/InheritedAlgebra.lean`,
`FaithfulAcceleration.lean` (the `weight_not_divergent` block); `tests/name_lint.py`;
`tests/run.py`.

**Not read, and named because it bears on the audit.**
`notes/LI_NATIVE_DEFERENCE.md` and its human register were read only through the
ledger's and roadmap's Stage V summaries and the `DECISIONS.md` queue entry that
points at them. Nothing in the August corpus touches computational futurity — the
Cartesian-frames document's own obstruction table already records Q4 as untouched
by anything on the table — so the round judged the summaries sufficient and did not
audit those two documents line by line. If the maintainers' Stage V ruling turns on
their exact wording, this round has not checked it. Likewise `FINITE_MODEL_SKELETON.md`,
`FUD_COMPARATOR_SPEC.md`, `FUTURE_AGENT_SPEC.md` and `TERMS.md` were not read: no
August material reaches the finite model.

## Files changed

| file | change |
|---|---|
| `projects/deference/README.md` | the source-material section names the current corpus, the recorded starting point, the audit's five-of-nine coverage, and the corpus's own unvetted status |
| `projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md` | evidence caveat repointed, with the coverage limit; the tower ⟹ Value row corrected and a paragraph stating it at exact strength |
| `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` | the *Exit — legitimacy* line disambiguates two live senses of the word |
| `projects/deference/notes/DISPATCH_QUEUE.md` | item 34 placed in wave 2; the round recorded as returned |
| `PRIORITIES.md` | deference-line context repointed (items 7, 8, 9, 14, 19) with the audit's module coverage stated; item 14's superseded source named; Q3 gains a second candidate; item 34 filed; friction entry F6 filed |
| `RESEARCH_STATE.md` | the deference section states the relationship to the source line |
| `DECISIONS.md` | one settled entry; the Q3 queue entry amended; two queue entries added |
| `PROVENANCE.md` | rows for this round, and its attribution line |

New: `prompts/2026-08-12-corpus-reconciliation/{PROMPT,REPORT}.md`,
`projects/deference/rounds/2026-08-12-corpus-reconciliation/{RECONCILIATION,FOR_HUMANS,PROVENANCE}.md`.

**Neither source tree was modified.** `git status` shows no path under
`note-dump-2026-06-27/` or `note-dump-2026-08-11/`.

## Major adjudications

1. **The August tree governs as current source material; the June tree remains the
   recorded starting point.** Taken as a settled decision, within scope, because the
   August receipt explicitly reserved it to the maintainers and this dispatch is
   that act. It adopts no content.
2. **Items 7–9 do not move.** Their evidence is byte-identical across the two trees.
   The one substantive addition is that the audit reaches five of nine modules, which
   is a limit on the items' evidence base and is now stated in both the items and the
   ledger.
3. **tower ⟹ Value is corrected, and no Lean is wrong.** §"Old claims corrected".
4. **The varying-question line opens no workspace track.** It strengthens the
   forward arrow, which the roadmap already records as largely inherited. Its one
   durable transfer — that a weighting may read less than a trader may — is the same
   conclusion the workspace's admissibility work reached from the authorization side,
   and is recorded as convergence rather than filed.
5. **The two lines reached structurally analogous non-recoverability results about
   different latent variables**, independently and roughly six weeks apart, the
   source line's earlier (2026-07-01 against Stage V's 2026-08-11). The workspace
   cannot recover an authorization from the realization map; the source line cannot
   recover an influence map from the observable trace. Both concluded the missing
   structure must enter the type. Recorded in `RESEARCH_STATE.md` and adjudicated in
   `RECONCILIATION.md` §2.1.
6. **The workspace's Movement V negative does not refute the source line's
   certificate program**, and the reason is that jurisdiction is a capability fact
   invisible to a valuation while the influence defect is a difference of two
   expectations. That asymmetry is the strongest evidence available that legitimacy
   and jurisdiction are two objects, and it is why no synthesis was forced.
7. **Q3 does not graduate, and is better specified.** Two candidates now fail on
   complementary axes — structure without time, time without authority — which
   constrains the missing object more than either did alone: it must carry temporal
   depth *and* explicit authorization or capability structure at once. No combined
   object has been built and nothing shows none exists.
8. **No corrigibility theorem is ready.** Four reasons, in `RECONCILIATION.md` §4,
   together with the sharpest statement of the target the evidence now supports.

## Old claims corrected

**One, and it is the round's substantive finding.** The ledger's Movement I carried
"tower ⟹ Value, asymptotic and finite" as `inherited-established` conditionally,
with the gloss that its Logical Induction facts "are named, not derived" — the
ordinary situation for every inherited row.

The source line refutes that arrow's **hard-selector route** at full menu-quantifier
strength. On a menu whose every option is worth nothing exactly when it is the one
selected, the tower holds — by a paper theorem, in the self-trust instance — while
Value fails. So no hypothesis quantified over all bet sequences implies Value
quantified over all menus, and the step that fails there is **hard** self-endorsement:
the expert's provable assignment of the max value to its own argmax selection.

Three things bound the correction, and all three are in the ledger:

- **No Lean is refuted.** That step enters the refuted route as an explicit
  hypothesis, which is what the named-hypothesis discipline exists for. The source
  line says so itself: the kernel check "is untouched — it always took the F1 carry
  as a named hypothesis."
- **What changes is the reading of the row.** The arrow was carried as available
  with its facts merely underived, and at full menu-quantifier strength it is not
  available. A scope condition on Value's own menu quantifier is necessary.
- **The port is soft, so it is not the refuted route — and that is where the
  correction stops.** `InheritedAlgebra.value_asymptotic` is a vanishing-gap mixture
  over the menu rather than the sharp selector, and the hard-argmax declaration was
  never ported. The source line separately reports a *fixed*-gap hedged construction
  as punishment-robust, at a stated grade — proved modulo an open
  feature-introspection step, the robustness flagged same-session, unvetted and not
  machine-checked. Resemblance between the two soft constructions is **not**
  identification. Whether the port's full hypothesis package is jointly satisfiable
  on that menu is **unestablished in both directions** and is item 34, which is
  written not to prejudge which hypothesis would fail.

The ledger row now reads `inherited-established` for the composition and open for
whether its hypotheses are jointly satisfiable at the strength the name suggests.

One pointer was corrected for the same reason: item 14 named
`note-dump-2026-06-27/notes/faithful-acceleration.md` as the context for stating the
strongest inherited theorem exactly, and the source line's adjudication found that
document's §5 strength ladder wrong and two of its lines false. The item now points
at the corrected statement and says what the old file is.

## New source results not adopted, and why

None of the following is registered, promoted, or entered in any ledger row. Each is
recorded in `RECONCILIATION.md` §1 with its path and the status its own page
declares.

- **Theorem A** (fixed questions are delay-proof under arbitrary delay, no
  visibility in either direction) — the source line's strongest statement. *Not
  adopted:* PROVED modulo named hypotheses at the source's own credence, unvetted,
  and it advances the forward arrow, which this line does not compete on.
- **Theorem SS** (scheduled quote–credence agreement on varying questions under
  one-way clearing) — same, plus its own load-bearing hypothesis (L) is a condition
  on what a weighting may read that the source line discovered late and used to
  correct two of its own pages.
- **The closed Total Trust / Value / Tower triangle**, the centred-bet squeeze, the
  refuted matching impossibility, the corrected trade-off bound, the LI paper
  erratum. *Not adopted:* all unvetted source results about the forward arrow;
  adopting them would change what this line says without changing what it holds.
- **The trace non-recoverability artifact** — kernel-checked in the corpus, and its
  own document calls it "a finite shadow … not an LI theorem," a four-day rational
  dynamical system with no inductors, traders or markets in it. *Not adopted:*
  kernel-verified in another tree is neither registered here nor a workspace result,
  and the workspace independently holds the analogous statement about its own object.
- **The legitimacy theory** — CONJECTURE/INTERPRETATION-grade by its author's
  declaration, with the two claims whose failure would sink it named and unproved.
  *Not adopted:* it is about belief where this line is about authority, and whether
  the program wants it is reserved.
- **The corpus's `wiki/` as a governing surface.** It governs the source line. This
  line's ledger continues to govern this line.

Vocabulary was deliberately not imported: no workspace surface gains the source
line's theorem names, its notion names, or its wikilinks. Where a source object is
named here it is named with its path.

## Priorities added, removed, reworded

**Added:** item 34 — instantiate the ported chain on the punishing menu and decide
per hypothesis. [entry]: the theorem is ported and building, the counterexample is
finite and exact, and the work is instantiating one against the other. A negative
answer is the more useful outcome and is stated as success.

**Added:** friction entry F6 — a pointer into a superseded source tree still
resolves and nothing marks it stale. This round paid it by hand across seven
pointers to learn that four were unchanged and one had materially changed.

**Reworded, not reformulated:** items 7, 8, 9 and 19's contexts repointed to the
current tree with the audit's module coverage stated; item 14's context repointed
with its superseded document named. No item's target, deliverable shape, acceptance
check or difficulty tag changed.

**Reworded:** Q3 gains a second candidate object and the constraint that follows
from the two failing on complementary axes.

**Removed:** none. **Retired:** none. Every other deference priority was assessed
against the dispatch's six questions and left standing; the assessment is that the
August corpus advances the forward arrow and the workspace's open items are all on
the reverse arrow or the market/trader gap, neither of which it touches.

## Decisions taken

One, above: the current-source ruling. It is a *which document governs* decision,
which `RESEARCH_STATE.md` records as maintainer-owned and `DECISIONS.md`-recorded,
and it was reserved to the maintainers by the intake receipt rather than left
undecided by oversight.

## Outstanding maintainer actions

1. **Rule on whether the source line's current frontier belongs in this line's
   ledger.** The round declined to describe it in Movement I on the ground that the
   ledger records what this repository holds. Queued in `DECISIONS.md` with the
   three options.
2. **Rule on whether endpoint-preservation is a target this program wants.** This
   is *what is worth proving* and no round may decide it. Queued.
3. **Note that the Q3 queue entry has changed while pending.** A second candidate
   arrived; the entry is amended in place and the ruling is unchanged in kind.
4. **Consider F6 for graduation.** The check it describes is cheap and fits the
   null-input discipline; whether to build it is not this round's to take.

No stale queue entry was found. The five entries predating this round all remain
live and none was resolved by its evidence.

## What this round does not establish

- **That any August result is true.** Nothing was re-derived and no Lean was
  rebuilt — not the source tree's, which carries its own toolchain, and not this
  repository's, whose gate is unaffected by anything here. Source credences are
  reproduced as source credences.
- **That the workspace's `value_asymptotic` survives the punishing menu, or fails
  it.** Item 34 exists because the round could not answer it by reading. The ledger
  states it as open in both directions rather than guessing from the hedged form,
  and a reader should not take the note that the port is hedged as an argument that
  it is safe.
- **That legitimacy and jurisdiction are provably different objects.** The argument
  is from what each line's results turn on. No theorem separates them and none is
  filed.
- **That the independent-rediscovery finding is more than structural.** Two theorems
  of the same shape about different objects are not a theorem about the shape, and
  nothing here proposes to make one.
- **Anything about Sam Eisenstat's position.** The source's own account is a
  same-day paraphrase by one party and is cited as one.
- **That the absent wiki pages contain what the corpus's index says.** Several
  load-bearing page names in that index are planned and not present. Every
  correction cited here is cited to a file that exists.
- **Item 14's own question.** Confirming the ledger's inherited rows against the
  source remains unperformed; this round repointed its context and corrected one row
  from the source line's own adjudication, which is not the same as rebuilding
  anything.

## Gates

`python3 tests/run.py`: all green. Six project runners pass; the seven gate
self-tests pass; the name lint is clean over 89 Markdown files; the Lean sorry and
axiom-discipline scans are clean over 14 files. The Lean build was not run — no Lean
changed, and the runner skips it without `WORKSPACE_LEAN=1`.

Two notes on running them. The lint reads `git ls-files`, so a first run over
unstaged new files reports clean while scanning none of them; the counts above are
from a run after staging. And the lint caught one real thing: `RECONCILIATION.md`
quoted the source corpus's own provenance warning verbatim, and that sentence names
a maintainer. Standard 7 wants source content cited inline rather than by label, and
the lint forbids the name in prose; both are right, and the resolution is to state
the warning's content and cite the two files that carry it, which is what the
document now does. Worth knowing for any future round quoting a source tree's
front matter, and not filed as friction — one paraphrase is not a structural cost.

---

## The final question

> After incorporating the August 11 corpus as evidence — but not automatically as
> canon — what is the strongest coherent picture we now have of the
> deference/corrigibility research program, and what single next piece of research
> would most increase our ability to prove a genuinely nontrivial corrigibility
> theorem?

**The picture.** The program has two arrows and they are now in very different
states. The forward arrow — can a bounded reasoner use a faster one as an
accelerator of its own deliberation — is in good health and is not ours: the source
line has a strong fixed-question result, a scheduled varying-question result, a
closed triangle among the three deference notions, and a run of impossibility
attempts that kept dying under verification, which is evidence for the positive
statements rather than neutral. The reverse arrow — can continuing corrective
authority run back toward the human-guided process — has produced almost nothing but
negative results, and those negative results are now the most valuable thing either
line holds.

What the reconciliation adds is that the negatives converge. Two research lines,
working on different objects without knowledge of each other, proved the same
theorem: the thing that matters is not recoverable from what the system emits. Ours
says a valuation over realizations cannot see who authorized an action. Theirs says
no function of the record can see how much of the principal's conclusion was the
advisor's. Both drew the same moral. That is no longer one line's methodological
quirk; it is the shape of the problem, and it means the program's remaining move is
structural — put the thing in the type — rather than inferential.

Where the two lines split is instructive rather than embarrassing. They certify: make
the advisor compute the counterfactual it alone can compute, publish it, and stake on
it. We protect: make the alternative unreachable, so that failing to identify the
principal stops mattering. And our own results explain why both are right for their
own object — certification cannot converge to jurisdiction, because tightening the
certificate shrinks the distinction it was meant to reveal, and that argument turns
on jurisdiction being a capability fact a valuation cannot price. Influence is not
such a fact. So the certificate route is closed to us and open to them, which is the
sharpest evidence yet that legitimacy and authority are two objects rather than one
word with two uses.

The corrigibility theorem itself is not ready and nothing in the corpus makes it
ready. What is now stateable, and is more constrained than what the program carried
before, is the shape: it must live in a type that simultaneously carries an
authorization relation no realization-valuation can see and a counterfactual
continuation indexed by where the advisor's channel was cut, and its conclusion must
be about what the principal can still *reach* rather than what it comes to *believe*.
Each clause is purchased by a failure. We have two candidate objects for that type
and they fail on complementary axes: Cartesian frames give structure with no time
coordinate, the sealed-sibling family gives a genuine time coordinate with no notion
of authority, and as each stands neither contains what the other supplies. Whether
an enrichment carrying both works — frames given a temporal index, or the sealed
family given an authorization or capability relation — is untried and open, and
nothing here argues it is impossible.

**The single next piece of research.** Build the two witnesses that decide whether
endpoint-preservation is a foreclosure notion or only resembles one: a case where the
principal's deliberative endpoint is preserved and its capacity to correct is gone,
and the mirror case. Both are finite, both are cheap, and the answer is
load-bearing either way. If they exist, the two candidate objects are genuinely
about different things and the program stops hoping the source line's construction
will supply what it needs — which frees Q3 from a candidate that was never going to
work. If one of them cannot be built, then on the relevant class the two notions
coincide, and the sealed-sibling family becomes the first object anyone has offered
this program with a real time index and a defensible claim to be about corrective
capacity — which is exactly the missing half of the type, and Q3 graduates on it.

That is the recommendation over the more obvious one. The obvious move is to chase
the corpus's new positive results, and it is wrong: they advance the arrow this line
does not compete on, they are unvetted, and adopting them buys narrative rather than
capability. The corpus's own recommendation points the other way — it names this
repository's formalization as where future verdicts should be discharged. The work
that repays is on this side of that boundary, and this is the piece of it whose
answer changes what the program does next in either direction.

Item 34 is smaller and should be done first, because it is an afternoon and it
decides whether a ledger row is honest. But it is hygiene. The witnesses are the
research.

---

## Review corrections

Three defects found in review of pull request #25 and corrected on the same branch.
**None changes the round's substantive verdict**, and none touches the source trees,
the priorities filed, the current-source decision, or the assessment that no
corrigibility theorem is ready.

### 1. Chronology of the two non-recoverability results

*Said:* that the two results were proved "eleven days apart", and that the
workspace's came first.

*Why it was wrong:* both halves are false, and the round asserted them without
checking either date. The source line's artifact is dated **2026-07-01**
(`projects/deference/note-dump-2026-08-11/deference-trust-lab/run3/work/trace-nonrecoverability/trace-nonrecoverability.md`,
header and compile line); the workspace's `StaticViewFactorization` landed with
Stage V on **2026-08-11**. The gap is roughly six weeks and the source line's is
the earlier.

*Now says:* the two lines reached structurally analogous non-recoverability results
about different latent variables, independently, roughly six weeks apart, with the
source line's earlier — and no priority claim beyond what the dated artifacts
support.

*Verdict unchanged.* The finding was never about who was first; it was that neither
derived the other, which is what makes the convergence evidence about the shape of
the problem. Getting the direction backwards was careless and load-bearing for
nothing.

### 2. Hard-selector versus soft-hedge conflation

*Said:* that the ported chain's `hSoft` is "the softmax bound standing in for the
expert's endorsement of its own selection", which the source line "now reports
**false** on selection-punishing menus" — and, in the ledger, that the failing step
is one "every version of the theorem takes as an explicit hypothesis."

*Why it was too strong:* it merged two different constructions. What the source line
refutes is the **hard-selector** route, whose failing step is hard self-endorsement
over a least-index argmax. The **soft** route is a different construction with a
different endorsement step, which the source line reports as punishment-robust —
and at a grade the round also failed to carry: proved modulo a feature-introspection
step filed as open, with the robustness observation flagged same-session, unvetted
and not machine-checked (`wiki/soft-self-endorsement.md` §"Status"). The port is
soft, so it is not the refuted route; but the source's hedged construction uses a
*fixed* gap where the port carries `δ → 0`, so the two are not identical on their
face either. Asserting the port's hypothesis false was exactly the question item 34
exists to answer, decided in advance and in the wrong direction.

*Now says:* the refuted route and the reported-robust route are named separately,
with the second's grade attached; the port is stated as soft and therefore not the
refuted route, and as not identical to the source's hedged construction either; and
both the survival and the failure of its hypotheses on the punishment family are
stated as unestablished. Item 34 is rewritten around two symmetric outcomes — the
port survives, or the package cannot be jointly instantiated — with an explicit
instruction not to prejudge which hypothesis fails and not to define success by
importing the source line's own scope condition.

*Verdict unchanged.* The ledger row still moves from "available, facts underived" to
"open at the strength the name suggests", and no Lean is refuted. What changes is
that the round no longer answers item 34 while filing it.

### 3. Non-composability overstatement

*Said:* that the two candidate structures for the foreclosure object "do not
compose", because "the second has no coordinate for the first to attach to."

*Why it was too strong:* nothing in the round establishes it. The observation
supporting it is that neither construction, **as currently formulated**, contains
the structure the other supplies — which is a fact about two existing formulations,
not an impossibility. A time-indexed family of frames, or a sealed-deliberation
model enriched with an authorization or capability relation, is exactly the sort of
object Q3 may require, and neither has been tried.

*Now says:* the two fail on complementary axes; no combined object has been
constructed; nothing shows none exists; whether an enrichment carrying both works is
open.

*Verdict unchanged.* Q3 still does not graduate, and what the correction sharpens is
the requirement rather than the answer: the missing object must carry temporal depth
**and** explicit authorization or capability structure at once.

### What the three have in common

All three are the same failure in different places — a real observation stated one
notch stronger than its evidence. Two dates not checked, a resemblance reported as
an identification, and a limitation of two formulations reported as a property of
the objects. Each was cheap to avoid by inspection, and the round's own discipline
section warns against exactly this: the second defect had the round pre-answering a
question it was in the act of filing as open.
