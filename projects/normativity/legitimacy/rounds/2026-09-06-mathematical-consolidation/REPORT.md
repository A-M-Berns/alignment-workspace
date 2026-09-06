# Report

## Result

`CONSOLIDATION.md` states the theory the canonical pages should now carry; `THEOREMS.md`
is its Lean ledger. The verdict is **READY FOR FULL CANONICALIZATION**.

What the mathematics settled:

- **Integrity ⇒ Answerability.** The right local primitive is not a conservation
  clause but a type: a transition supplies an *account* for every live port, and the
  account type has constructors only for the three fates and authenticated local laws.
  Conservation, faithful carry, receipt immutability and occurrence multiplicity are
  consequences (`OccurrenceIntegrity`). PR85's lattice ledger is an instance.
- **Settlement.** Six conditions that shared the name "settlement integrity" have six
  homes; only counterfactual suppression is a Robust Openness matter, and only when the
  application routes through settlement.
- **Legitimacy.** `Leg_P = Segment × RobustOpen_P`. Diachronic Answerability's content
  half is a theorem of the segment; its standing half is `(P)` at the null
  intervention. PR85's A6 is the exact counterexample to deriving standing from
  Integrity, and no new primitive is needed.
- **Non-Capture.** Given actual coverage, PR85's `(S, R+, P)` is Robust Openness
  itself (`certPlus_iff_robustOpen`). The substantive external bill is componentwise
  route persistence, strictly stronger (`persistence_not_necessary`).
- **Progress.** The canonical statistic is the transport-weighted edge loss plus
  residual, as in PR82. The headline endpoint PR85's `progress_bound` proved is
  distinct (`edge_headline_separation`) and optional. The canonical bound is
  `edge_progress_bound_quadratic`, typed on the Integrity export as
  `Evaluation.progress_bound`.
- **Normative Inductor.** Two conditional theorems replace `EndToEndHypotheses`, whose
  conclusion had returned six opaque premises. `deductive_normative_inductor` composes
  the registered effective end-to-end theorem through to the Progress bound, deriving
  the uptake certificate from conformance.

## Dependencies

Takes as hypotheses: `2026-09-05-integrity-synthesis` and the five rounds it rests on;
`2026-09-04-normative-inductor-realization` for the Progress endpoint;
`2026-09-03-defeat-landing-horty-standing` for the Defeat Principle reading of a
disposal as an identity law. Cites without depending on: the September checkpoint's
`LEGITIMACY_DECOMPOSITION.md`.

## Deviations

- The dispatch was executed in two parts. A Codex worker (`PROGRESS.md`, prompt
  `prompts/2026-09-06-mathematical-consolidation/workers/progress.md`) repaired the
  Progress endpoint and drafted `OccurrenceIntegrity` and the interface module before
  running out of budget; this round rewrote both drafts and completed the rest.
- The CI repair in `HistoryIntegrity.lean` moves the audit block outside the namespace
  rather than setting `pp.fullNames`, matching every other module.
- `EndToEndHypotheses.end_to_end` was deleted rather than relabelled. It was
  introduced by the unmerged PR85 and its conclusion restated its hypotheses.
- The Codex draft's `LocalLaw.realize : Evidence r ≃ Π Evidence (child i)` was weakened
  to two maps without round-trip laws; the equivalence's inverse laws had no normative
  content and were not used.
- `Evaluation.loss` takes the anchor, not the occurrence. The draft's occurrence
  argument was redundant with the anchor and would have let a loss depend on identity.

## What this does not establish

- That any implementation authenticates a `Protocol`: `Admitted`, `Live`,
  `Authorized`, `AnswerOK`, `SetView`, `Closes` and every `LocalLaw`'s maps are inputs.
- Inhabitation of the LI hypotheses of `conditional_normative_inductor`; the
  certificate half is inhabited, the market half is not.
- Inhabitation of `DeductiveProcessComputation` for `deductive_normative_inductor`;
  it inherits the registered theorem's status.
- Necessity of each protocol predicate individually; the blocks in
  `CONSOLIDATION.md` §2 are by typing, and PR85's countermodels remain the necessity
  evidence for the record layer.
- That the null intervention belongs to every application's `J`; this round adopts it
  as the meaning of Robust Openness and records the decision.
- Anything about liveness, rates, or asymptotics.

## Proposed later maintainer consolidation

`CONSOLIDATION.md` §11 is the migration map. The canonical pages can be rewritten from
§§2–8 without a further conceptual round; the two queued rulings (protected
principal; settlement independence) change what the text commits to, not what it says.

## Outstanding maintainer actions

1. Rule on the two queued `DECISIONS.md` entries this consolidation touches: whether
   the legitimacy predicate may name a protected principal (the P-indexed form is the
   only one that exists), and whether settlement independence is standing or
   per-realization (either way it is `Protocol.SetView`'s authenticity plus source
   trust, two inputs).
2. Decide whether this branch supersedes PR85 (it contains PR85's commits) or lands
   after it; the pull request is opened against `main`.
3. Dispatch the canonicalization pass against `CONSOLIDATION.md` §11
   (`PRIORITIES.md`, *Canonicalize the legitimacy spine from the consolidation*).

## Attribution

- Prompt author: maintainer, relayed verbatim.
- Executor of `PROGRESS.md` and the first drafts of `OccurrenceIntegrity.lean` and
  `NormativeInductionInterface.lean`: GPT-6 (OpenAI), as a Codex worker.
- Executor of the consolidation, the final Lean modules, and this report:
  Claude Fable 5.1 (Anthropic).
- Dates: 2026-09-05 to 2026-09-06.
