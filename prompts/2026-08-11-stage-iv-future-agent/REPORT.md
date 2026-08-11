# Stage IV parent report — the future agent is still not in the model

Maintainer: A. M. Berns
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Executor-model: Claude Opus 5 (Anthropic)
Date: 2026-08-11
Branch: `round/2026-08-11-deference-corrigibility`
Review status: `ci-only`

Stage IV was dispatched to construct a genuinely later, better-informed, fallible agent
before any FUD theorem, on the discipline *do not prove a theorem about a future agent
until there is actually a future agent in the model*.

**It did not.** A stop condition fired: the independent review found a conceptual collapse
with no cheap repair. The construction is kept as a diagnosis, the claimed-gate harness is
deleted, and the round's positive reading is withdrawn.

---

## 0. Verification

| check | result |
|---|---|
| `lake build` | 1844 jobs, exit 0 |
| axiom audit | 160 results across 11 files, all within the allowance |
| `tests/run.py` | green |
| sorry gate | clean over 11 files |
| `diagnose_collapse.py` | exit 0, **13 checks, each recording a defect** |

The superseded harness claimed 28 checks in the round's first reporting. It ran **23**;
the figure was carried over from Stage III without being checked. Recorded because an
unverified count is exactly what this repository's standards exist to catch.

## 1. What was attempted

Three credences instead of one: `P` for the present evaluator (and the pricing measure),
`P̂` for the later agent, `P̄` for the principal. The later agent maximises *its own*
expectation on *its own* information `σ`, which refines the principal's `τ`. The intent
was that `P̂ ≠ P` makes the later agent's rule something other than the evaluator's argmax,
so that it can be better informed and still wrong.

## 2. Why it fails

**The later agent is still derived.** `κ_A` differs from the evaluator's conditional argmax
by exactly one argument. It remains a total function of `(P̂, σ, X)`, all declared known at
`n`. A different credence buys the freedom to name, on each cell, an action optimal under
*some* measure; it does not buy a process the evaluator lacks. In the headline instance the
transferred arm's realisation is **constant** — `a` at all four states — so the evaluator
does know the realised action, which is precisely what the gate existed to rule out. The
check meant to catch this could not fail: its second disjunct was a module constant.

**Jurisdiction does no mathematical work.** Setting `P̄ := P̂` with the full-signal interface
makes the delegated arm **identical to the transferred arm at every one of 32,805
instances**. The transferred arm is a *coordinate* in the delegated arm's parameter space —
`(interface bandwidth, deciding credence)` — and `J_n` occurs in no formula. Verified
independently before acceptance.

**The dominance result is Stage III's theorem with the arms swapped.** Under the
action-recommendation interface the transferred arm's realisation *is* the message, so the
claim reduces to "the maximum over a cell is at least a member of it". Stage III put the
evaluator's argmax on the transferred side and the transferred side trivially won; Stage IV
puts it on the delegated side and the delegated side trivially wins. Same tautology, other
arm. The Lean corollary already said it was `envelope_dominates` reused — what the round
failed to draw was the conclusion that this makes its only theorem the collapsed one.

**And the scan behind it is padding.** 19,468 of 26,244 instances contain no fallible later
agent at all — they are Stage III instances, the configuration this round existed to
eliminate — and 21,186 of the remainder are ties.

## 3. Three further claims were false

- **Advice loss.** The round said the loss came from the later agent's error being baked
  into the message. It does not: under a Bayes-rational principal a wrong recommendation
  costs nothing, because the principal re-optimises on the message cell. The loss is
  **bandwidth**, and it vanishes under a *more* fallible agent whose recommendation
  happens to separate the cells.
- **The interior requirement.** "Fallibility requires the later agent's information to have
  interior" is false as stated; it needs an unstated full-support hypothesis on `P̂`. The
  corrected observation cuts against the design: this agent can be wrong only where an
  argmax can be moved by reweighting, which measures how derived it remains.
- **The fairness accounting.** `τ` was the trivial partition in every instance tested and
  was never varied, so the principal was *blind* rather than merely coarser. The round
  cannot distinguish "transfer wins because the principal is fallible" from "because the
  principal sees nothing".

## 4. The finding worth keeping

> Two authorisation regimes that induce the same realisation map `Ω → Π_n ⊔ {⊥}` are the
> **same object** in a signature whose only outputs are such maps priced by one measure.

This is not a modelling slip that a fourth parameter repairs. It is a **type-level
obstruction**: a jurisdiction assignment is exactly what such a signature cannot express.
It explains, retrospectively, both prior failures — Stage III "found no jurisdictional
term" in a model that had deleted the execution layer, and Stage IV added a credence and
found the two arms extensionally identical. Neither was going to work, for the same reason.

It also sharpens `PRIORITIES.md` Q3 ("what quantity prices who holds authorization?") from
an open question into a near-impossibility: **no valuation-shaped object over realisation
maps can price a jurisdiction assignment**, and a successor must either put the
authorisation relation in the type or prove that nothing can.

## 5. The twenty questions

1. **Did we construct a genuine future agent?** No.
2. **In what sense is it later?** Only in that its information index is later. Its rule is
   a present-computable function.
3. **In what sense better informed?** `σ` strictly refines `τ`, and the best `σ`-measurable
   policy beats the best `τ`-measurable one. That part is real.
4. **Can it be wrong?** Yes, but only where an argmax can be moved by reweighting — which
   is a symptom of its being derived, not evidence of independence.
5. **Can `A_n` evaluate it without knowing its action?** In general yes; **in the round's
   own instance, no**, because the realisation is constant.
6. **Is the execution layer live?** Partly. `⊥` carries a declared quantity and is selected
   in 8,996 of 26,244 scanned instances, but it is selected nowhere in the displayed
   instance.
7. **Is `⊥` live?** See 6 — live in the scan, decorative in the headline.
8. **How is jurisdiction represented?** It is not. `J_n` appears in no formula.
9. **What differs between D and FU?** The pair (conditioning partition, deciding credence).
   Not jurisdiction.
10. **Is future cognition held fixed?** Yes — the later agent's rule is identical in both
    arms. This is the one fairness property that holds.
11. **Is advice loss explicit?** It is computed, but its stated cause is wrong (§3).
12. **Does it pass the anti-collapse tests?** No. Collapse 1 (present argmax) and Collapse 3
    (jurisdiction absent) both fire; Collapse 5 fires for the dominance hypothesis.
13. **What did the red team find?** §2–§3 and `REPORT-red-team.md`.
14. **What competence debt remains?** Unchanged and unaddressed: the cardinal hypothesis
    with its unbounded near-indifference leakage.
15. **Does Track I's collapse still apply?** Yes, and now at two levels — to the competence
    hypothesis, and to `P̄ = P`, which *is* the conclusion rather than a hypothesis for it.
16. **What does LI contribute?** Nothing yet. This is finite decision theory; no result here
    should be cited as a Logical Induction theorem.
17. **Is underwriting absent from the main engine?** Yes — it appears nowhere. This survives.
18. **Is FUD ready for theorem research?** No.
19. **The single controlling obstruction.** The type-level one in §4: the model's signature
    cannot express a jurisdiction assignment.
20. **What should the paper claim?** §7.

## 6. Does the FUD program survive Stage IV?

**Comparator still not coherent** — and the reason is now known to be structural rather
than a sequence of modelling mistakes.

Two rounds have failed in the same place from opposite directions, and §4 explains both.
That is progress of a real kind: the obstruction has moved from "we keep building it wrong"
to "here is why this class of model cannot hold it". But it is not a comparator, and no
FUD theorem is available.

**What survives across Stages III–IV:** the envelope theorems, correctly named; the
reduction of the comparator gap to the delegation deficit; the confirmation that
underwriting is absent from the engine; the confound witnesses; and the type-level
obstruction, which is new.

## 7. Aspirational versus constructed

**Aspirational mathematical claim.** Under non-circular competence and a fair comparison,
the incremental value of giving a future AI jurisdiction is bounded.

**Constructed mathematical state.** Finite envelope theorems and their competence bound,
kernel-checked and unregistered; three confound witnesses; two collapse diagnoses; a
type-level obstruction to pricing jurisdiction in a realisation-map signature.

**Mathematical gap.** Everything between. There is no future agent, no jurisdiction object,
and therefore no comparator.

**Aspirational philosophical gloss.** Future cognitive superiority need not justify
transferring final jurisdiction.

**Constructed philosophical gloss.** *Only this:* a valuation over realisation maps cannot
distinguish who authorised an action, so the question cannot be settled in that register —
which is a claim about the register, not about jurisdiction. Nothing established here bears
on whether transferring jurisdiction is justified.

## 8. Research debt

| kind | before | after |
|---|---|---|
| model debt | two missing objects (future agent, jurisdiction) | **unchanged in count, sharper in kind**: now known to be a type-level obstruction rather than an unbuilt component |
| assumption debt | cardinal competence + leakage | unchanged |
| theorem debt | no FUD theorem | unchanged |
| formalization debt | low | low — nothing new promoted |
| interpretation debt | high | **reduced**: two collapse modes are now documented with witnesses |

**Did Stage IV convert model debt into assumption/theorem debt?** No. It converted *some*
model debt into an impossibility-shaped question, which is a better form of the same debt
but not a discharge of it.

## 9. What was not established

1. **No future agent, no comparator, no FUD theorem.**
2. **The type-level obstruction is argued, not proved.** §4 is a structural observation
   supported by an exhaustive check over 32,805 instances of one parameterisation. It is
   not a theorem that no valuation-shaped object can price jurisdiction.
3. **Nothing about whether transferring jurisdiction is good or bad.**
4. **`τ` was never varied**, so nothing here is evidence about a merely-coarser principal.
5. **Nothing is registered**, and nothing is maintainer-reviewed.

## 10. Deviations

1. **The round's own positive reading was withdrawn** after the review, as in Stage III.
2. **The claimed-gate harness was deleted rather than repaired.** Ten of its twenty-three
   checks could not fail and seven labels overclaimed; repairing it would have preserved a
   construction the review showed is not worth repairing.
3. **An earlier review run was destroyed by the orchestrator.** Repairing an unrelated pull
   request conflict involved a `git stash` that removed the still-untracked artifacts
   mid-read. Recorded in `REPORT-red-team.md`; the artifacts were committed before the
   re-run.
4. **A reporting error is corrected**: the harness ran 23 checks, not the 28 first reported.
5. **Tracks were not run as separate agents**, as in Stage III; only the red team was
   independent, which the dispatch requires.

---

## Human register

The instruction for this round was blunt and correct: do not prove a theorem about a future
AI until there is actually a future AI in the model. The previous round had failed by
writing the future AI's decision as a formula the *present* AI could already evaluate, so
its "future agent" was the present one's own best plan wearing a costume.

We tried to fix that by giving each party its own beliefs. The present evaluator has one
set, the future AI another, the human a third. The future AI now decides by its own lights
rather than by the evaluator's, so it can be well-informed and still get things wrong. That
seemed like the missing piece.

It was not, and an independent reviewer showed why in a way that is hard to argue with. Our
"future AI" still differs from the previous round's fake one by a single symbol: which set
of beliefs goes into the same formula. Everything about it is still computable in advance
from things we already wrote down. In the specific example we led with, its decision was the
*same action in every possible world* — so the present agent knew exactly what it would do.
The check we had written to catch that mistake was broken in a way that made it impossible
to fail.

The deeper problem is the one worth remembering. We wanted to compare two worlds that differ
only in *who has to sign off*. But our model describes a world purely by which action ends
up happening in each state, and how much that is worth. If two arrangements produce the same
actions, they are literally the same object in our mathematics — there is nothing left to
tell them apart. And we could show this concretely: set the human's beliefs equal to the
AI's, give the human the AI's full information, and the "human decides" arm becomes
*identical* to the "AI decides" arm, in every one of thirty-two thousand cases we checked.
Authority was never a variable. It was a name we were putting on one setting of two dials.

That is why both attempts failed, and it is genuinely useful to know. It is not that we kept
building the model slightly wrong. It is that this kind of model — describe what happens,
price it, compare — cannot express the difference between an action you took and an action
someone authorised you to take. Adding more detail to the beliefs will never help. The
permission structure has to be part of what the model is made of, not something we hope to
read off the outcomes.

We also learned something uncomfortable about our own arithmetic. Half the time, our future
AI was exactly indifferent between its options, and its "decision" was really the order we
happened to list them in. Two of our five conclusions reverse if you write the list
backwards. All the numbers were exact — no rounding anywhere — and that protected us from
nothing, because the fragility was never about precision.

So Stage IV is a second negative, and it did not produce the object it was asked for. What
it produced instead is a reason to stop trying this way.

---

## Outstanding maintainer actions

1. **Accept or reject the negative verdict** (§6). Everything downstream depends on it.
2. **Do not dispatch a FUD proof round, and do not dispatch another comparator round of this
   shape.** Two attempts have now failed at the same place for the same structural reason.
3. **Decide whether §4's obstruction should be attacked as an impossibility.** It is
   currently an argued structural observation with an exhaustive check behind it, not a
   theorem. Proving it would convert the program's central negative from a repeated
   observation into a result — and would say that jurisdiction is architectural on
   mathematical grounds rather than by the program's choice. This is the highest-value item
   the round produced.
4. **Note the repeated harness failure mode.** Stage III shipped four checks that could not
   fail; Stage IV shipped ten, including a literal `True`. A mechanical lint — flag any
   check whose condition is a constant, a type test, or contains `or True` — would have
   caught both, and is a cheap maintainer act.
5. **Rule on whether `FUTURE_AGENT_SPEC.md` v1 is kept as a corrected defective record** —
   its current state — **or withdrawn.**
6. **Review the research-state PR.** Not merged.
