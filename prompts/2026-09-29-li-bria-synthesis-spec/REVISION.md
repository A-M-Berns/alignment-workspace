# Revision dispatch — review of the first pass (2026-09-29)

Relayed verbatim as sent by the maintainer in the same Claude Code session, after the
first pass had been pushed as PR #115.

---

Revise PR #115’s LI/BRIA specification round in response to the review below. This remains **specification and validation work**, not a construction round.

The first pass usefully distinguished predictor access, scoring granularity, negative controls, and criterion-level versus construction-level guarantees. Preserve those improvements. However, several mathematical claims need correction, and the specification has become too closely identified with the existing continuation-BRIA architecture.

The objective remains:

> Give crisp, defensible acceptance criteria for a computable LI/BRIA synthesis, so that satisfying them would justify calling it a substantive improvement over previous approaches to logical-induction decision theory.

Independently verify the review’s objections. If an objection is mistaken, supply the precise argument resolving it. Otherwise correct every affected document, fixture, report, and summary. Do not merely append caveats while leaving stronger claims elsewhere.

### 1. Repair the cross-subsidy analysis

Proposition P2 claims that the proposed paying agent is a BRIA. Its estimates are zero on heads, where it receives one, and one-half on tails, where it usually pays and receives zero.

The apparent counterexample to coverage is:

- On heads, propose the sole available action with promise one.
- On tails, propose an available action with promise zero.

This hypothesis outpromises on every heads round, is executed there, and has no negative test losses. The fixture checks particular refusing hypotheses but misses this hypothesis.

Check this against the exact paper definition, including permissible test sets. If the objection holds:

- Retract P2 as a BRIA witness.
- Retain the example only for what it actually demonstrates: global no-overestimation alone permits cross-subsidy.
- Add a focused regression check for the missed heads hypothesis.
- Reassess P1 and the claimed conclusion that the conflict is *exactly* between belief–decision compatibility and commitment.
- Determine how much of the per-round mugging obstruction follows from BRIA itself, under the stated hypothesis class and predictor assumptions. A short direct argument is appropriate; do not launch a broader construction search.

Distinguish coverage of a few fixed bidders from coverage of the full comparison class. Also check adaptive and time-varying promises wherever a statement quantifies over all efficient hypotheses.

### 2. Audit R4 without presupposing its derivability

The proposed derivation of belief–decision compatibility has at least these apparent gaps:

**Subsequence gap.** Global no-overestimation does not by itself imply no-overestimation on every market-generable weighting. Explain what additional argument would establish the stronger property.

**Cumulative-loss gap.** Asymptotic unbiasedness does not prevent a bidder’s cumulative reward-minus-promise record from tending to negative infinity. For example, errors of order \(-1/\sqrt{k}\) have vanishing average but divergent cumulative loss. Therefore, an accurate market-expectation bidder is not automatically protected from BRIA refutation.

**Computational-access gap.** A construction being computable in its larger runtime does not automatically make its selected action, test sets, or rejection sets accessible to the efficient hypotheses or LI traders. State the actual complexity and continuity/generability conditions required.

**Semantic gap.** R4 defines the realized score of the selected continuation, but its derivation then uses a score variable for an arbitrary alternative continuation. Define that variable and its settlement rule, including what happens when the continuation is not selected. Do not assume the missing counterfactual semantics through notation.

**Timing gap.** Specify the order of market publication, hypothesis evaluation, action selection, and any post-selection forecast. Distinguish a forecast that guides selection from a forecast formed after learning the selected action.

For each gap, either repair the argument with explicit hypotheses or identify the claim as unresolved. Separate:

1. R4 as an independently proposed requirement.
2. R4 as a conjectured consequence of other requirements.
3. Any weaker compatibility statement that is actually established.

A countermodel to derivability does not itself satisfy R4. Correct the acceptance checklist’s “theorem or countermodel” language accordingly: a countermodel informs revision of the specification; it is not a passing synthesis.

Do not describe R4 as derivable unless the argument supports that claim.

### 3. Separate the general research target from the block specialization

The current candidate type requires system-scheduled blocks, published estimates, and binding execution of a selected continuation. These are substantive modeling choices.

Reorganize the specification into:

- **General acceptance requirements:** the epistemic, decision, accountability, and interaction properties sought from a synthesis.
- **A continuation-BRIA specialization:** how those requirements might be instantiated using the existing block interface.

Do not require every candidate to publicly announce numerical claims merely because the current BRIA construction does. Distinguish internal estimates, mathematical witnesses to a recovery theorem, and publicly observable outputs.

Likewise, distinguish:

- commitment supplied by an external execution contract;
- an agent choosing to enter such a contract;
- stability of the agent’s own future decisions without external enforcement.

Avoid excluding modular architectures. An LI whose prices materially inform a BRIA could be a genuine synthesis. The target is substantive interaction with proved guarantees, not architectural unity for its own sake.

Preserve the existing continuation-BRIA results and their role as a useful specialization. Do not let that specialization predetermine the general answer.

### 4. Correct the interpretation of the interaction and prediction tests

**T10: logical information and action.** The fixture compares three blind predictors with a hypothesis receiving the current truth from an oracle. Keep it as an interface illustration if useful, but do not call it a general LI–BRIA separation theorem.

Distinguish eventual settlement from information available before action. Learning a sentence after a computable delay does not automatically provide an accurate forecast before the relevant decision.

State what additional theorem would turn this illustration into an LI-based interaction diagnostic. A failure of each individual blind predictor on its own subsequence also does not automatically prove a limitation on an adaptive learner combining them.

**T8: Agent Simulates Predictor.** Retain the explicit access models, but do not claim the original problem reduces to publication of a commitment without proving that equivalence. A predictor able to read an externally supplied commitment channel is a materially different environment. Compare the benchmark against its primary-source formulation and say exactly what is preserved or changed.

Apply the same discipline throughout the suite: a changed predictor, newly supplied commitment mechanism, restricted menu, or oracle must be visible as a change in assumptions—not counted as solving the original problem.

### 5. Clarify what would constitute a serious advance

Distinguish two levels of achievement:

1. **A substantive synthesis theorem:** coherent logical beliefs coupled to accountable decision learning, with precise LI and BRIA recovery and a meaningful interaction result.
2. **An advance on a recognized LI decision-theory obstacle:** a result addressing at least one existing difficulty under a matched, explicitly stated environment and information structure.

Identify a small number of candidate diagnostics for the second level. We do not need a solution yet. We need a defensible success condition and an explanation of why existing guarantees do not already deliver it.

Do not manufacture an advance by providing a new oracle, making a commitment externally enforceable, changing predictor access, or silently restricting the comparison class. Those may be legitimate conditional results, but their contribution must be stated accurately.

One-shot success is not mandatory. A repeated setting can qualify if it preserves the relevant obstruction and the improvement is visible to the proposed guarantee.

### 6. Deliverables and stopping point

Update the existing problem statement, test suite, audit, and report rather than creating another sprawling layer of documents.

Conclude with:

- A short recommended core specification.
- The continuation-BRIA specialization, clearly marked as such.
- Corrected mathematical findings, including the status of P1, P2, and R4.
- A small set of substantive advance diagnostics.
- Remaining choices requiring human research judgment.

Keep source-backed results, proved deductions, conjectures, and finite illustrations visibly distinct. Run checks appropriate to the edits, but do not treat passing fixtures as proof of quantified asymptotic statements.

Stop before searching deeply for a construction. The success condition for this round is a research target whose mathematical claims and benchmark interpretations we can trust.
