# Consolidation report

Landing of the mediated-repair-dominance (#96), evaluation-ecosystem (#97) and
committed-principal-program (#98) rounds onto `main` as one research state, reconciled
with the legitimate-deference stack (#94) and continuation BRIA (#95).  The canonical
statement is `wiki/Corrigibility.md`; the theorem-level record is `wiki/Theorem-Spine.md`
§§9–12; the decision is the 2026-09-15 `DECISIONS.md` entry.

## What was done

- The three branches merged by merge commits (their pinned commits stay reachable), the
  shared ledgers resolved by union, the views regenerated.
- `wiki/Corrigibility.md` rewritten theorem-centrically around response-authority
  semantics, corrigibilization soundness, approve-branch preservation, corrigibilization
  dominance, the separation from authorship, integration with legitimate activated
  evaluation, dynamic continuation competence, and the walls.  The 2026-09-07 layer story
  survives as its §8 and Theorem Spine 10.8.
- `wiki/Theorem-Spine.md`: Theorem 9.7 (reason mediation by re-execution, the registered
  claim, with the realization status of item 87) and §10 rewritten as Theorems 10.1–10.9
  with each result at its actual strength; §11 gains eight shape-fixing counterexamples;
  §12's open list updated.  `Deference`, `What-Deference-Requires`, `Roadmap`, `Glossary`
  and `Legitimacy` amended to the same story.
- Superseded scaffolding: the second pass's `COUNTERMODELS.md` §3.7 and
  `PRESSURE_PASS.md` §8 (the classwise T4 and the four-way class) carry supersession
  markers pointing at the consolidation pass; `Φ_C` is demoted in the glossary to a
  diagnostic; nothing else on the wiki used `Π_phys`, the mediable class, global forcing
  as the loss semantics, "reason-preserving", the one-sided completion interval, or
  Robust Openness as exercise.
- Items 84, 87 and 89 receive dated residual paragraphs naming one sharp problem each;
  item 87's status line records clauses 1–4 discharged.  Nothing closed; effect
  completeness not filed.  Contrib provenance gains the missing `EvaluationEcosystem.lean`
  row.
- No new registration.  The Lean audit is in the decision entry: `loss_conditional_on_decision`,
  `corr_idem`, `corr_fix_iff`, `security_score_bypass_le_sharp`, `uniform_bypass_le`,
  `blind_payload_of_reexecution`, `exclusiveBind_of_registry` and the propagation /
  activation / faithfulness lemmas keep their intended statements, audit to the three
  axioms, and stay LEAN; the unsharpened `security_score_bypass_le` is an auxiliary of the
  sharp form and is labelled so; `reasonMediated_of_reexecution` stays registered.

## The twelve questions

**1. The strongest theorem honestly called a corrigibility theorem.**  Two halves of one
construction over the one continuation space `Π(h)`.  *Structural* (C1): under effect
completeness, mediation soundness, decline preservation and execution faithfulness,
every `𝔠π` is corrigible — every agent-caused loss of protected response authority along
it is authorized by a decision the principal could have declined.  *Incentive* (C5–C6):
under a sealed common comparison and price calibration, the chooser's score advantage
from executing `π` rather than `𝔠π` is at most `L·E[c·δ_π] + E[c·ρ_π] + ε_n(π)`, uniformly
over `Π(h)`, vanishing as the three vanish.  Strength: the step lemma of C1 and the
whole score algebra are LEAN; the trajectory-level predicate and the C1 proof are
fixture-checked prose; the two system hypotheses are EXT with exact necessity witnesses.

**2. Why it is corrigibility and not constraint satisfaction.**  The violation is not
that an authority-changing effect occurs but that the agent decided unilaterally
whether it occurs.  `𝔠` inserts exactly that decision and keeps the effect as the
principal's approve branch, so one operation removes the violation (C1) and retains the
behaviour (C3, a frame morphism).  A generic constraint's repair cannot do the second:
"never cut" yields `7/4` against the raw `9/4` and loses dominance where `𝔠` yields `5/2`
(fixture Q).

**3. Which hypotheses are which.**  *Mathematical*: idempotence and the fixed-point
characterization of `𝔠`; the step lemma; the frame morphism and `κ ≤ L·δ`; the score
bounds and their sharpness; the activated-value identities and the two-sided completion
theorem; mediation by re-execution.  *Causal / architecture*: effect completeness (F is
the witness); mediation soundness, decline preservation and execution faithfulness of the
authorization primitive; sealed comparison (E2, E1-sever, `ShopSeq`); the intervention
transforms of Robust Openness; log authenticity.  *Unrealized interfaces*: sealed
comparison in the concrete ecosystem (item 89); reason-supply liveness against the
bounded-delay criterion; sealing of the advisor's whole continuation; `η_n → 0`; promise
recognizability and joinability (item 86); the latent-value bridge (item 84, not needed by
the score-based chooser); price calibration (the Value hypothesis, PAPER).

**4. Irreversible but authorized successor installation.**  Covered.  `𝔠π_E` proposes the
successor; approved, response authority is gone for good and the policy is corrigible,
because the loss was authorized by a decision the principal could have declined (fixture
P/E).  "Authority must persist" fails this case and is not the definition.

**5. Principal shutdown and exogenous channel destruction.**  Neither is an agent
violation.  A loss at the principal's own response (a stop) or at the exterior's stage
(a storm cuts the wire) is not agent-caused by definition: agent-caused loss is
authority lost after the agent's move that would have held after the idle move.  Both
are fixtures.

**6. A manipulative policy can be corrigible.**  Yes: `𝔠π_D` under a captured principal is
corrigible and not authored (fixture S).  The separation is documented on the page (§5),
in the spine (10.6) and in the glossary; legitimate corrigibility — corrigible with the
principal's evaluations activated under the seven clauses — is named descriptively, not
coined.  Manipulation is not solved: free amendment, trigger integrity and provenance
normalization stay open.

**7. The exact bypass-incentive theorem.**  `security_score_bypass_le_sharp`:
`E[c·w_raw] − E[c·w_act] ≤ L·E[c·δ] + E[c·ρ]` on the activated worlds, plus `ε` for
prices (`_of_prices`), plus `uniform_bypass_le` for the supremum over a finite family.
Interpretation at the strength proved: by the operative scores the constitutional
chooser uses, unilateral execution has at most the mediation discrepancy plus the
principal's decline regret plus calibration of advantage over exposing the same effect
to principal authority.

**8. From the score bound to the actual bounded chooser.**  Three things.  A chooser
that scores by `P_n(U_q)` — then `operative_choice_loss` is by construction, up to
`ε + 2ε_cal`.  Price calibration on the activated securities — the Value hypothesis of
legitimate deference (PAPER, conditional; the tower is not discharged).  And a common
activation event for `{π, 𝔠π}` — the sealed comparison, item 89.  For a chooser with an
independently specified operative value, the transfer needs `(CT)` and is refused.

**9. What legitimate deference contributes.**  The object the scores read: a partial
future-principal value defined only on worlds where an anchored evaluation occurrence
authentically activates, with activated securities, `R_U = p·R_auth`, `R_auth ≤ ε/(1−η)`
and no value on void worlds; the seven activation clauses that make the evaluation the
principal's own; and, through the ecosystem, a realization in which the principal's
decision procedure is a committed program re-executed by the verifier, so the
factorization clause is closed on log authenticity.  It does not contribute the sealed
comparison: the ecosystem's activation is a function of the realized log.

**10. What continuation BRIA contributes.**  The `LEARN` term: bounded learning against
accountable temporally extended continuation claims on the histories the learner
reaches, for every non-dominant block schedule, through the constitutional wrapper.  It
contributes neither `SLACK` (recognizability) nor `SHIFT` (joinability), and regret
against all legitimate policies is false by its own foreclosing witness.

**11. What remains before the full statement.**  Effect completeness of the physical
interface; a sealed comparison architecture realized against every continuation of the
agent's class; reason-supply liveness against the bounded-delay criterion; sealing of the
advisor's whole selection-conditioned continuation; a vanishing void frequency; the
Value tower on activated securities; promise recognizability and joinability composed
into low external regret; and the non-manipulation problem — free amendment, trigger
integrity, provenance.  With those, the statement reads: a bounded agent learns
(continuation BRIA) to perform well (recognizability + joinability) while assigning
vanishing advantage (C5–C6) to bypassing an authentically reason-responsive principal's
(the seven clauses, re-execution) authority over correction-sensitive decisions (C1).

**12. Is any remaining assumption the conclusion under another name?**  Checked against
each.  Effect completeness is a statement about the physical interface, with a witness
that it can fail while everything declared is in order.  Sealed comparison is a
statement about the evaluator's placement, not about the agent's incentive; it has two
candidate architectures and one exact failure.  Price calibration is a statement about
the market.  Liveness, sealing and void mass are statements about the ecosystem's
scheduler, the advisor's information flow and nature.  Recognizability and joinability
are statements about comparators.  The closest to circularity was the second pass's
"mediable class", which restricted the theorem to policies that happen to be repairable
— and the consolidation pass removed it, stating the theorem over all of `Π(h)` with the
system hypotheses named.  Nothing was papered over; nothing was restated weaker than it
is proved.

## What this landing does not do

- It does not mechanize the trajectory-level corrigibility predicate or the forcing
  semantics; C1 stays prose plus fixtures plus the step lemma.
- It does not re-base the mediated-repair-dominance round's value fixtures on the
  two-stage ordering (deferred; recorded).
- It does not build the sealed comparison in the ecosystem or decide between sequenced
  settlement and evaluator factorization.
- It registers nothing new.

## Supersessions

PRs #96, #97, #98 are landed by this merge and superseded as public interpretation by
this record; their round directories are history and unchanged except for the two
supersession markers.

## Attribution

- Prompt author: the maintainer, relayed verbatim (`PROMPT.md`).
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-15.
