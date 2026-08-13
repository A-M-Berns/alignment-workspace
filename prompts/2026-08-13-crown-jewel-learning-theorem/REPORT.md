# Report

**Prompt-author model:** GPT-5.6 Sol (OpenAI)
**Executor model:** Claude Opus 5 (Anthropic)
**Dates:** dispatched and executed 2026-08-13
**Verdict:** `CROWN-JEWEL-PATH-POSITIVE / DYNAMICS-STRENGTHENING-OPEN`

The round's documents carry the results. This answers §XXX's twelve questions and
records what belongs to the round.

## §XXX, answered

**1. The exact strongest theorem.** In `CROWN_JEWEL_THEOREM.md`. For every
certified surgical repair `g` in a fixed finite class, one Blum–Mansour learner
gives `R_T(g) <= B_T(g)` simultaneously, hence
`Q_T(g)/M_T(g) <= B_T(g)/(delta_g M_T(g))`, hence the conditional rate vanishes
whenever `B_T(g) = o(M_T(g))`.

**2. Sublinear regret is a conclusion**, produced by the construction, never a
hypothesis of the crown jewel. `ASSUMPTION_AUDIT.md` has the split. Only the
asymptotic corollary is stated conditionally on a rate, and says so.

**3. What is learned away.** Numerator: mixed mass on one source response at dates
its reason is due. Denominator: the number of those dates. Not `T`.

**4. The weakest coverage condition** is `B_T(g) = o(M_T(g))` — for a `sqrt(T)`
bound, `M_T(g) >> sqrt(T)`. Weaker than positive density, and sharp: at
`M_T = Theta(sqrt(T))` the ratio is constant and the conclusion fails.

**5. Yes, for a schema.** The acknowledge repair's margin is derived from the loss
construction under a public side condition — no new exposed content, nothing
precluded. Predicted `1/2`, measured `1/2`. Not derived for the class, and one
repair in the class has margin `-2`.

**6. Repair-language adequacy can legitimately stay a hypothesis**, provided it is
stated. What cannot stay implicit is the new recurrence condition in
`REPAIR_LANGUAGE.md`: a class can be adequate in expressivity and still make its
own conclusions vacuous.

**7. The construction complies immediately.** For any class whose rules point away
from mistakes with no return route active at the same date, the targeted response
is transient in the rule-mixture chain at exactly the selected dates, so
`Q_T(g) = 0` identically.

**8. It matters to the word, not to the theorem.** The theorem is unaffected; what
fails is the diachronic reading the programme's own prose promises.

**9. Not identified.** What is needed is a no-regret learner against the same
surgical class whose distribution is *not* the fixed point of the current rule
mixture. The fixed point is what makes swap-type regret self-consistent, and the
algorithms in the audited source all compute one. Whether an alternative exists is
open and is stated as the concrete question, not answered.

**10. Replay remains optional** and is refuted as a target — level 7 of the ladder.
Levels 0–2 do not touch it.

**11. Coverage is where corrigibility composes**, in shape. The merged deference
result gives a corrective capability surviving every advisor policy; coverage needs
an *exercise rate*. That is one assumption, not a new formalism, and no arc
supplies it. Stated as a target, not claimed.

**12. Three blocking items** — coverage, repair-language adequacy, compiler
soundness — in `PATH_INVENTORY.md`, with sequencing.

## What is new in this round

**The denominator.** The merged round read `Q_T` against `T`. That is the wrong
denominator and can be vacuous: under a sparse schedule a learner mishandling every
selected occasion still has `Q_T/T -> 0`. The conditional rate is the quantity that
means learning-to-respond, and switching to it *weakens* the coverage hypothesis
from density to `o(M_T)`.

**The margin, derived.** H5 moves from hypothesis to conclusion for a schema.

**The transience characterisation.** Exactly: absence of a return route. The
identity self-loop does not rescue a state. Tested across three classes.

**The dynamics verdict, with a control.** The engine *is* feedback-responsive — on
a class where the target is recurrent the within-class share moves, freezes when
the margin goes to zero, and does not move under an uninformative loss. A
normatively coherent class removes the occasion for it.

## Deviations from the dispatch

1. **No Lean**, again. §XXIII asks for the reusable lemma to be formalized unless
   there is a concrete reason not to. The reason is budget: a local `lake build`
   was attempted in the previous round and did not complete inside the round, and
   shipping unverified Lean into a repository whose Lean gate is load-bearing is
   worse than shipping none. Filed as the top formalization item.
2. **§XIII's policy-regret literature branch not opened.** It is conditioned on the
   primary path failing; the primary path did not fail. Level 7 is recorded as
   refuted from the merged round's own evidence rather than re-investigated.
3. **The alternative-learner question is named, not answered.** §XII asks to
   inspect primary literature if the diachronic notion matters. The round
   establishes that it matters only to the interpretation, not to the theorem, and
   stops there rather than opening a literature review the verdict does not turn
   on.
4. **`LearningEvidence` is a criterion object, not a measurement harness.** The
   pre-registered clauses are checked against numbers obtained in probes and
   recorded in `LEARNING_DYNAMICS.md`; the test asserts the criterion's logic and
   the recorded values rather than re-running the learner inside the suite.

## What this round does not establish

- No Lean, nothing registered, nothing kernel-checked.
- Coverage and repair-language adequacy are hypotheses. The theorem is conditional
  on being asked, and P8 displays a vacuous satisfaction.
- Compiler soundness is absent: "lawful" names a discipline, not a proved property.
- The margin is derived for one schema only.
- Regret was never measured against its own bound.
- No pathwise statement, no anytime construction.
- The corrigibility composition is a shape match with a missing exercise rate.
- The reducible-chain observation is about this implementation's stationary
  solver, not about Theorem 18.

## New names introduced

All **provisional**: `answerability process`, `certified surgical repair`,
`conditional bad-response rate`, `margin-certified repair`, `learning-rate
coverage`, `recurrence adequacy`, `return route`.

## Structural defects found

None.

## Outstanding maintainer actions

Nothing is reserved. No `PRIORITIES.md` item filed, nothing appended to
`DECISIONS.md`, no claim registered, no decision requested. The PR is opened and
not merged.

The next target is named: coverage, because it is blocking, because it is where
the corrigibility arc plausibly composes, and because the composition needs one
assumption rather than a new object.
