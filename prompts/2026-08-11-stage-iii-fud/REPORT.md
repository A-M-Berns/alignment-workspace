# Stage III parent report — the FUD comparator, and why this one is not it

Maintainer: A. M. Berns
Prompt-author-model: GPT-5.6 Sol (OpenAI)
Executor-model: Claude Opus 5 (Anthropic)
Date: 2026-08-11
Branch: `round/2026-08-11-deference-corrigibility`, from `50cc2bc`
Review status: `ci-only`

Stage III asked whether fully updated deference can be stated as a fair, non-circular
comparison in which future cognition is held fixed and the changed variable is
jurisdiction.

**The round built a comparator, claimed it was fair, and was wrong.** An independent
adversarial review (Track F) established that the constructed `FU` arm contains no future
agent at all, and the round accepted the finding. This report states the defect, what
survives it, and what a successor must supply. A stop condition fired and is recorded
rather than worked around.

---

## 0. Verification baseline

| check | before | after |
|---|---|---|
| `lake build` | 1843 jobs | **1844 jobs**, exit 0 |
| axiom audit | 142 results / 10 files | **159 results / 11 files**, all within the allowance |
| library theorems | 155 | **170** |
| `tests/run.py` | green | **green** |
| sorry gate | clean | **clean over 11 files** |
| `verify_fud_comparator.py` | — | exit 0, **28 checks** |

The new module is reached by the default target without an import edit — the first
confirmation of the Stage II build repair on new content.

## 1. The defect

The round defined the transferred arm's selection as

```
φ(C) = argmax_π E_{P_n}[ X_{n,π} | C ]
```

— the argmax of **the evaluating agent's own objective under the evaluating agent's own
credence**, over the later partition. `A_n` knows `P_n`, `X` and `𝓕_{g(n)}`. So `A_n` can
compute `φ` at time `n`, and the `FU` arm confers no cognition `A_n` lacks. No object
representing `A_{g(n)}` distinct from `A_n`-conditioned occurs anywhere in the model.

What the round actually compared is the principal's contingent plan against the **optimal
later-measurable plan**: the envelope. Stage II priced that envelope and said in terms
that it *upper-bounds* every `FU[g]` and is not one. Skeleton v2 §4 declared `FU[g]` a
hole and warned that careless invention is how it collapses. **The round invented
carelessly in exactly the way it had been warned against**, and neither of Stage II's two
named prerequisites — time-indexed `A_t` semantics, and a jurisdiction-transfer object —
was delivered.

Three consequences.

**The dominance result is trivial and was mislabelled.** `envelope_dominates` carries one
hypothesis — that `φ` is a per-cell maximiser — and no fairness condition whatever. It is
`∑ maxima ≥ ∑ anything`. Its original docstring said "under the fairness conditions",
describing a statement that did not exist. The fairness conditions are a shared-argument
convention, not hypotheses.

**Its driver is infallibility, not "epistemic improvement only".** An agent that
conditions the evaluator's own credence on the evaluator's own objective computes the true
conditional maximum by construction: it cannot be better-informed *and wrong*. The harness
now carries a witness — same partition, same menu, same objective, same evaluator, a
better-informed but **fallible** future agent — in which the gap is strictly **negative**.
The sign of the comparison is therefore fixed by a modelling choice, not by anything about
authority. The original label `F6` ("no evaluative drift") understated this badly.

**The "no jurisdictional term" reading was guaranteed by construction.** The specification
waived `⊥` and deferred all capability structure, deleting skeleton v2's execution layer —
which Stage II recorded as the place *all* of protection's valuation content sits — and
then observed that no jurisdictional term appeared in the resulting arithmetic. That is a
property of the datatype, verifiable by inspection, and it is not evidence about
jurisdiction. The regret identity itself is distributivity of subtraction over a finite
sum.

## 2. What survives

**Kernel-checked, and true at their real strength.** Fifteen theorems in
`EnvelopeDominance.lean`, renamed from `JurisdictionTransfer` to match what they prove:
the envelope dominates any cell-measurable selection; the gap decomposes into per-cell
regrets; agreement implies a zero gap; per-cell and aggregate gated-calibration bounds
with an inhabitation witness. These are reusable by any successor that supplies a real
future agent. What was wrong was the reading, not the mathematics.

**The fairness apparatus and its confound witnesses**, which are the round's most portable
output. Each witness now moves exactly one variable:

- **Information.** The principal's grades are the *same state-level function* in both
  models; only its information partition is coarsened. The gap moves from `0` to `1`, the
  carriers' maximum. A comparison that does not equalise the information time reports the
  value of information as a case for transferring authority.
- **Agenda.** With genuinely per-arm menus, widening only the transferred arm's menu
  moves the gap from `0` to `1`.
- **Fallibility and drift.** Two distinct failures of the future-agent model, both
  flipping the sign.

**The reduction, which stands independently of the defect.** The gap *is* the delegation
deficit against the later-measurable comparator class, so Track I's credence collapse
applies to the same object rather than by analogy: the supremum over credences is the
maximum pointwise regret, attained at a point mass — verified at coarse cells as well as
singletons. Any credence-free hypothesis bounding it is it. This holds for the envelope
comparison and would hold *a fortiori* for a genuine `FU[g]`, since the envelope
upper-bounds it.

**Two corrections to the round's own inputs.** The competence slot was misclassified as
Stage II's `PC-5`; it compares grades to a conditional expectation, so the credence occurs
in it, making it a **joint competence–credence hypothesis** under skeleton v2 §2a. This is
the same error the competence track caught for grade trust, repeated. And the claim that
all seven fairness conditions were machine-verified was false: three are checked, three are
construction conventions, and `F7` is unrepresentable because `μ` is not a variable of the
model.

## 3. Does FUD survive Stage III?

**Not well-posed as constructed.** The strongest honest verdict from the dispatch's list.

The round did not produce a FUD comparator; it produced an envelope comparison and
mistook it for one. The philosophical target — that the value of future cognition is not
the value of future jurisdiction — was **not** tested, because the model contains neither a
future agent whose cognition could be varied nor a jurisdiction assignment whose value
could be priced.

This is not a null round. The defect is precisely located, the two missing objects are the
same two Stage II already named, and the successor requirements are stated in §4. A
comparator that deletes the execution layer cannot answer a question about jurisdiction,
and knowing *why* is worth more than the positive reading the round briefly had.

**No claim is made that FUD is false, or that jurisdiction has low value.** Both were
outside what this model could see.

## 4. What a successor must supply

1. **A future agent with independent existence** — its own credence `P_{g(n)}`, or its own
   estimate `X̂` of the value quantity — so that *better-informed* and *correct* come apart.
   Without this the comparison's sign is a definitional artifact.
2. **Skeleton v2's execution layer, reinstated**: `κ_n`, `ρ_n`, `ι_n`, `E_n`, `⊥`, and a
   **declared `X_{n,⊥}`**. This is the carrier in which a jurisdiction assignment is
   something a valuation can price rather than a label on a selection.
3. **A jurisdiction mode `μ` as an actual variable**, which then makes `F7` statable.
4. **A competence hypothesis that is credence-free**, or declared as joint.
5. **A decision on `F2`.** It is an advice-losslessness assumption, and it trades directly
   against the comparison's non-triviality: the more completely the principal's information
   equals the AI's *and* it acts on it, the closer the arms come to identical.

Only after 1 and 2 does the round's question become falsifiable. The positive program is
confirmed only if, under a fallible future agent and a live protection structure, the gap
is still signed for reasons that are not the definition of `φ`.

## 5. The nineteen questions

1. **Is FUD well-posed?** No, not as constructed. §3.
2. **What is transferred at `n`?** In this model, nothing — `μ` is described in the spec
   and never carried.
3. **What information does each arm receive?** The same, by `F2`, which is an assumption
   of lossless advice at the level of measurability.
4. **What cognition?** The same — and that is the defect: the transferred arm's cognition
   is the evaluator's own, available at `t(n)`.
5. **What evaluative target is fixed?** `X`, scored by `A_n`, in both arms.
6. **Is future `A` epistemically improved only?** No — it is modelled as *infallible*, and
   §1 shows this is what drives the result.
7. **What does `H⁺` receive?** Advice, modelled only by the measurability it confers.
   Message alphabets and lossiness are not modelled.
8. **Competence assumption on the advised principal?** Margin-gated cell calibration —
   a joint competence–credence hypothesis, not `PC-5`.
9. **The near-indifference leakage?** `2B` times the ungated mass, unbounded, and the
   harness reports that only 9,476 of 164,868 satisfying instances have a bound informative
   enough to beat the free `2B`.
10. **The jurisdiction-transfer value quantity?** There is none in this model. The quantity
    computed is the envelope gap.
11. **Does self-assessed uncertainty matter?** Not for this comparison; the slot stayed
    empty.
12. **Is quote-responsive gating still a blocker?** Not here. Open for the certificate line.
13. **Is underwriting load-bearing?** No — it appears nowhere. This survives the defect and
    is a genuine negative.
14. **Is refusal separate?** Yes, and trivially so, because `⊥` was waived — which is
    itself part of the defect.
15. **Is agenda controlled or scoped out?** Scoped out by hypothesis, with a corrected
    witness.
16. **What stands between the model and a FUD theorem?** The two objects of §4.1–4.2, which
    are Stage II's prerequisites 1 and 2, still undelivered.
17. **Is there a serious theorem ready to dispatch?** No.
18. **If yes, state it.** N/A.
19. **The single controlling obstruction.** A future agent that can be better-informed and
    still wrong. Everything else in §4 is downstream of it.

## 6. Assumption audit

| assumption | class | status |
|---|---|---|
| `φ` is the true conditional maximiser | definitional | **the defect.** Presented as `F6`; it is infallibility, and it alone produces the dominance result |
| `F2` same information | information symmetry | **assumed**, and an advice-losslessness assumption in disguise |
| `F4` agenda symmetry | agenda control | assumed, with corrected witness |
| `F1`, `F3`, `F5` | definitional | construction conventions, **not checked** |
| `F7` no future leak | timing | **unrepresentable** — `μ` is not a variable |
| margin-gated cell calibration | **joint competence–credence** | assumed; misclassified in the first draft |
| near-indifference leakage control | competence | absent; bound informative in 5.7% of satisfying instances |
| protected jurisdiction, `⊥`, `κ_n` | architectural | **deleted from the model**, not assumed |
| underwriting | settlement | **absent from the engine** |

## 7. What was not established

1. **No FUD comparator, and no FUD theorem.**
2. **Nothing about the value of jurisdiction**, in either direction.
3. **The dominance result establishes nothing about authority** — it is `∑ max ≥ ∑ any`.
4. **The regret identity is a tautology** and no weight rests on its missing terms.
5. **The rubber-stamp biconditional is false.** Only one direction holds; the counterexample
   is carried in the harness.
6. **The collapse was verified on small domains**, not proved over the skeleton.
7. **The gated bound has no sharpness witness** on its informative set.
8. **One decision index**; foreclosure remains inexpressible.
9. **Nothing is registered**, and nothing is maintainer-reviewed.

## 8. Deviations

1. **Tracks A–E were run as one design pass, not as separate agents.** They are coupled
   through a single object and splitting them risked the incompatible-objects stop
   condition. Track F was run independently, as required. In hindsight the coupling is
   also how the defect survived to Track F: no first-wave track was positioned to ask
   whether the `FU` arm contained a future agent.
2. **Track G was not run**, per the dispatch's instruction not to force it.
3. **A stop condition fired** — "jurisdiction transfer cannot be represented without
   changing the object-level decision problem", and arguably "the comparator cannot isolate
   jurisdiction from information". Recorded, not resolved by strengthening assumptions.
4. **The round's own first-draft conclusions were withdrawn** after Track F. The withdrawn
   readings are listed in §1 and in `REPORT-track-F.md`; the earlier framing is not
   preserved elsewhere, because it was wrong rather than superseded.
5. **The Lean module was renamed** from `JurisdictionTransfer` to `EnvelopeDominance` to
   match what it proves.
6. **Two root reports were deleted** at the maintainer's instruction during this round —
   an unrelated request, recorded in `DECISIONS.md` with its pointer repairs.

## 9. Provisional names

`envelopeGap`, `cellValue`, `cellMass`, `IsCellMaximiser`, `envelope_dominates`,
`envelopeGap_eq_regret`, `agreement_gap_zero`, `gap_le_of_gated_calibration`, `D`, `FU`,
`μ`, `advice interface`, `fairness conditions F1–F7`, `(AGENDA)`. None proposed for
permanence.

## 10. Executor attribution

Executed by **Claude Opus 5** (Anthropic), model id `claude-opus-5`, 2026-08-11. Prompt
author: GPT-5.6 Sol (OpenAI). Track F executed by a separate Claude Opus 5 context with no
access to this report. Review status: `ci-only`.

---

## Human register

The question was the one the whole project turns on. A future AI will know more than the
person it answers to. So why shouldn't it arrange, now, to be the one deciding later? To
ask that honestly you build two futures identical in every way except who signs off, and
measure the difference. If handing over control is barely better, corrigibility has a
rational basis and not only a moral one.

We built that comparison, checked it carefully, got a clean answer — and then an
independent reviewer, working from the artifacts alone with no idea what we hoped to find,
showed the comparison was not the one we thought we had built.

The error is worth stating plainly because it is instructive. We wrote the future AI's
decision as "whatever maximises expected value, given what will be known then." That
sounds like a description of a smarter future agent. It is not. It is a formula the
*present* AI can already evaluate, because it uses only the present AI's own beliefs and
its own goals. So our "future agent" was not an agent at all — it was the present agent's
own best contingent plan, written out. We had compared the person against a plan, and
called it a comparison against a future mind. An earlier phase of this project had
explicitly flagged that exact substitution as the trap to avoid, and we walked into it.

Once that is seen, the rest follows. Our headline result — that handing over control is
never worse — turned out to be the statement that a maximum is at least as large as
anything else, which is true and says nothing about authority. And the property we were
most pleased with, that no term corresponding to "and also the AI would be in charge"
appeared anywhere in the arithmetic, was guaranteed in advance: we had built a model with
no representation of being in charge in it. Finding nothing there is not a discovery.

What is genuinely useful survives. We have machinery for catching the three ways this
comparison can be rigged — give the AI better information, give it more options, or let it
want different things — and each is now a worked example that moves exactly one variable.
We know the comparison reduces to a question already on the books rather than opening a new
one. And we know precisely what a real version needs: a future AI that can be
better-informed and *still wrong*, and an actual representation of who has to authorise an
action. We built a witness for the first of those, and it is sobering — as soon as the
future AI can be wrong, handing it control can be strictly worse, and the sign of the whole
comparison stops being determined by anything except how we chose to define it.

So Stage III did not answer its question. It established that the question had not yet been
asked properly, located the two missing pieces exactly, and left the machinery for asking
it again. That is a real result, and a much better outcome than shipping the confident
version we had four hours ago.

---

## Outstanding maintainer actions

1. **Read §1 and decide whether the round's negative verdict is accepted.** Everything
   downstream depends on it.
2. **Do not dispatch a FUD proof round.** The comparator does not yet exist. §4 lists what a
   successor needs, and items 1 and 2 there are Stage II's prerequisites 1 and 2.
3. **Rule on whether `FUD_COMPARATOR_SPEC.md` v1 is kept, corrected, as a defective record**
   — its current state — **or withdrawn.** It is currently marked as not a binding input.
4. **Note the repeated classification error.** The competence slot was misclassified in the
   same way grade trust was in the previous phase. A mechanical check — does the hypothesis
   mention the credence? — would have caught both, and filing it as a standing lint is a
   cheap maintainer act.
5. **Consider whether first-wave tracks should carry an explicit "does this object exist
   independently?" obligation.** The defect survived because no track owned that question.
6. **Review the research-state PR.** Opened per the dispatch's §24, which explicitly
   contemplates a PR when a stop condition fires and the branch records the obstruction
   cleanly. Not merged.
