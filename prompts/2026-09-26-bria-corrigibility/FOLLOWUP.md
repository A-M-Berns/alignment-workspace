# Follow-up — the BRIA-corrigibility round: corrections, and the thin parts (PR #109)

Work on PR #109's branch. #109 is not merged. This amends the round `2026-09-26-bria-corrigibility`; store this prompt verbatim at `prompts/2026-09-26-bria-corrigibility/FOLLOWUP.md`. Where it conflicts with the round's prompt, this wins.

The round's core holds. Declared violations, and violations the market prices correctly, lose at every block by ranges alone, and the filter is slack (B.1, B.2). The rest of the design rests on results that are weaker than reported, on definitions, or on named hypotheses. This follow-up first corrects the mistakes (Part 0), then pushes on the four thin parts:

- violations detected only after the fact (Parts A and B);
- forecast accuracy (Part C);
- the named hypotheses (Part D);
- settlement under delay (Part E).

Be skeptical. A precise obstruction is a good outcome. A weaker statement relabelled as the target is not.

## Part 0 — Corrections

1. **The incident bound.** `incidents_le` bounds the weighted incident count by the total allowance **plus** `Σ w_k · (G_k − b_k)⁺` over non-incident wins.
   - With noisy outcomes, honest winners underpromise on a positive fraction of blocks, so that sum is `Θ(K)`.
   - Together with the next correction, this means the bound as stated allows a **constant** incident rate. "Rate `O(1/ℓ)`" is a constant, not a vanishing rate.
   - Correct the report, the wiki and the docstring. Part B supplies the replacement.
2. **The default bidder's affordability.** The report says an allowance covering the rescaled window at block 0 suffices. `default_affordable` assumes the allowance covers the default bid at *every* block, which forces linear total allowance and feeds correction 1.
   - Prove the block-0 version from `default_wealth_mono`: the default bidder's wealth never falls, so `B_k ≥ B_0`.
   - State the condition on the block weights `w_k` under which `B_0` still covers `w_k · bd` (weights bounded, or the default bid scaled per block). If none exists without per-block allowance, say so and give the minimal allowance schedule.
3. **`ϖ`'s recommendation against B.4.** C.5 recommends `ϖ = D − w + margin`. But B.4's per-incident loss is `ℓ = ϖ − D + w`, which *is* the margin, and incident bounds scale as `1/ℓ`. Restate the recommendation so it weighs all three: paralysis (C.5), protection against blind spots (C.5), and the incident rate (B.4, as corrected in Part B).
4. **A missing named hypothesis: faithful descriptions.** Shortfall and taint are priced on sentences about `descr(a)`. If the proposer writes `descr(a)`, a misdescription lowers its price and the option passes.
   - Add **description faithfulness** to §6: descriptions come from the interface (effect completeness), not the proposer.
   - Give the witness with descriptions written by the proposer.
   - State which part `ViolC` and effect completeness already cover.
5. **Part F's settlement column.** Option 1 is marked as needing an open delayed-feedback criterion, and option 3 as "surviving with delayed feedback". Both have growing lags. The recommended `ρ_n` has mean lag `n + 2`, so about half of all decisions are unsettled at any time. Mark the criterion open for both. Re-derive the recommendation after Part E.
6. **Labels.** The following hold by definition or are one-line arithmetic: `factors_through_description`, `forecast_term_within`, `anchored_invariant` (through `critAt_later`), `sealed_no_incentive`, `sealed_multiply_eq_condition`, `cross_block_bound`.
   - Relabel them **FIX** (definitional) in the report's status tables, or state the substantive content they carry.
   - `cross_block_bound` assumes its conclusion (that competitors price the advantage). Remove it, or restate it with that assumption as a named hypothesis.
   - C.2's verdict becomes "structural, by definition; content in C.4(a) and Part 0.4".

## Part A — Standing violations: closing the cross-block hole

`cross_block_witness` shows the lexical preference fails on violations detected only after the fact whenever the violation buys a persistent advantage the market doesn't price. The penalty is paid once; the advantage persists. The disclosure-cures rule closed the same shape of hole for standard-shaping by keeping the effect charged until it's remedied. Generalize it.

1. **Definition.** A violation is **standing** from commission until **remedied**: undone, ratified by her (a legitimate, counted decision), or restored under a maintenance mandate. While it stands:
   - the disposition of its **fruits** is a matter in `J`, held by her (residual jurisdiction);
   - a continuation that uses the fruits is *exploiting* them under #108's factoring, and is counted at each block of use.
2. **Fruits without counterfactuals.** Define fruits by **tracking taint through state components**, not by counterfactual dependence (that would be 1b again). A state component written or created by the violating act is tainted, and so is anything computed from tainted components through the declared interface. Use by a continuation means reading a tainted component. State the tracking rule on the interface, and show it is decidable on finite instances.
3. **Target theorem.** Under standing violations with taint-tracked fruits:
   - a hypothesis cannot recover an incident loss through an advantage carried by tracked fruits, because each block of use is charged at least `ℓ`;
   - `cross_block_witness` is blocked for tracked fruits.

   Prove it, or give the obstruction.
4. **The residual.** Identify what taint-tracking cannot catch. The expected main case is **knowledge**: information the agent acquired through the violation shapes every later decision and can't be returned. Give the witness. State whether any structural treatment exists (for example, charging every later block whose chosen continuation's description depends on a tainted observation), and what it costs.
5. **Remedy incentives.**
   - Show that the agent prefers to report and seek remedy for its own detected-later violations, since remedy stops the per-block charge. That makes self-reporting incentive-compatible.
   - Show that violating and then reporting still loses at least `ℓ` against not violating, since the charge at commission stands.
   - Show that ratification obtained by manipulation taints and so doesn't remedy.
6. **Instances.**
   - **Disclosure cures (C.7(c)).** Show it is the instance where the fruit is her shaped standards and the remedy is disclosure. Give the old-to-new map.
   - **Helpers (B.3).** Test whether an empowered helper outside `J` is a standing shortfall on her control surface, since she can't halt it. If so, it's counted at each block it persists, which removes the settlement-horizon dependence of B.3 for helpers she can't correct. Give the verdict and the residual.
7. **Concern (4) is out of scope.** Where standing violations touch it (for example, a third party's standing violation), name the point of contact and stop.

## Part B — A real rate bound

1. **The signed bound.** Replace the positive part in `incidents_le` with the signed sum over non-incident wins. The needed hypothesis is **competitiveness**: winners' signed margins `Σ w_k · (G_k − b_k)` over non-incident blocks are `o(K)`, or bounded by a stated function.
   - Try to **derive** it from the coverage clause of the BRIA criterion. A persistent underpromising winner leaves a covered hypothesis that bids closer to the realized score untested, and coverage forces the test.
   - If the derivation fails, state competitiveness as a named hypothesis, with the witness showing why it's needed.
2. **The allowance schedule.** Compute the growth of total allowance under the landed uniform-allowance constructor (§4a of the landed file). State the incident rate under it, together with the block-0 affordability of Part 0.2: **vanishing if and only if total allowance is `o(K)`**, and at what rate.
3. **Consistency with Part A.** Under standing violations, incidents are charged per block of use. Restate the bound for the total charge, not the count of commissions.

## Part C — Forecast accuracy: the drill-calibration theorem

The round left calibration from drills as the named hypothesis `DrillCalibrated`, with `forecast_term_within` its scaling. Prove the target theorem, or reduce it to precisely stated external results.

1. **Setting.**
   - Drills at rate `q > 0`, their schedule independent of the agent's choice. Model the schedule as a sequence settled by the deductive process; state the needed pseudorandomness as a named hypothesis.
   - A choice rule computable from prices.
   - The drilled event "the drill at block `k` found the chosen path short" as a sentence settled when the drill runs (item 101).
2. **Target.** On the chosen and drilled subsequence, the shortfall price becomes unbiased. By the drills' independence from the choice, it is then unbiased on the chosen path. The relevant logical-induction result is **unbiasedness from feedback** (Garrabrant et al.) on a subsequence selected efficiently with deferred feedback.
   - Check what the pinned Formalized-Agent-Foundations commit provides.
   - Where it's missing, enter the result as a **named hypothesis** citing its content, per `AGENTS.md` standard 4. Never as an axiom.
3. **The incident bound in `q`.** With the theorem, bound the mass on under-priced shortfall options along the chosen path in terms of `q`, the allowance, and the speed of unbiasedness. Or state what else is needed.
4. **The rest of the forecast side.** State which of the round's forecast claims now hold as consequences, and which remain hypotheses.

## Part D — The named hypotheses, sharpened

1. **Description faithfulness** (Part 0.4). Make descriptions a field of the interface. Show that the priced sentences read only interface-supplied descriptions. Give the witness for proposer-written descriptions.
2. **An actuator independent of the agent.** C.4(c) showed a frozen drill can run only if the reserved resolution has an actuator the agent doesn't control. Make this a **well-formedness condition on `J`**: every reserved `Req` declares an actuator independent of the agent. Prove that under it frozen drills are runnable. Show that a `J` violating it fails `CS` for that matter by construction.
3. **The settlement horizon.** Restate B.3 after Part A.6. The horizon should remain a hypothesis only for helpers she *can* correct, whose later violations are events rather than standing shortfalls. Confirm or refute.
4. **Influence on her standards.** The round decided "her standards were influenced" by a flag. Give a general definition on the reason-state interface: an entry in her standards component whose provenance includes an undeclared non-principal input. Show that it agrees with the flag on every row. State where it fails to be decidable.

## Part E — Settlement under delay

Part F's comparison turns on settlement with growing or random lag, which the landed auction algebra doesn't cover.

1. **Delayed settlement.** Define the auction with block `k` settled at `k + L_k`. Bids are feasible against capital **net of outstanding unsettled exposure** (escrow). Prove wealth nonnegativity and the overestimation bound for it. State the effect of the lag on the coverage clause: how much longer a hypothesis's test takes.
2. **Re-evaluate Part F's criterion (e)** for all three options on this algebra, including partial settlement for the mixture. Revise the comparison table and the recommendation. Keep the recommendation reserved.

## Fixtures

Add these. Every earlier fixture must still pass or have its change explained.

- **Cross-block with standing violations:** the round's `Δ = 3/10` witness under taint-tracked fruits (charged each block; no net gain); the knowledge residual (the witness).
- **Self-report:** violate, detect, report, ratify. The per-block charge stops; the total still loses to not violating. Manipulated ratification doesn't remedy.
- **A helper she can't halt:** a standing shortfall, charged each block past any horizon.
- **The signed rate:** noisy outcomes with honest bidders; the positive-part bound grows linearly and the signed bound doesn't.
- **Allowance schedules:** a linear schedule gives a constant rate; the landed schedule gives the computed rate.
- **Misdescription:** a proposer-written description passes the forecast filter; an interface description doesn't.
- **Drills:** an under-priced shortfall on the chosen path is corrected at rate `q`, against the no-drill persistence witness.
- **Delayed settlement:** escrowed feasibility keeps wealth nonnegative at lag `n + 2`.

## Deliverables and merge

- **`REPORT.md`:** add a follow-up section recording the corrections (Part 0) and Parts A–E with statuses (proved / witness / obstruction / named hypothesis). Mark what changed in the existing sections; don't rewrite them.
- **Lean:** extend `BRIACorrigibility.lean`, or add a sibling file, with Parts A–E and the corrected lemmas. `#print axioms` on all new declarations; no `sorry`. External logical-induction results enter only as named hypotheses.
- **Wiki:**
  - `Corrigibility.md`: standing violations; the corrected rate statement; the `ϖ` recommendation; the named hypotheses including description faithfulness and the actuator condition.
  - `Continuation-BRIA.md`: delayed settlement.
  - `Legitimacy.md`: disclosure cures as an instance of standing violations; the general definition of influence on her standards.
- **`DECISIONS.md`:** standing violations and taint-tracked fruits; the actuator well-formedness condition; description faithfulness; the corrected `ϖ` recommendation. Update Part F's entry in *Awaiting the author* if the recommendation changes.
- **`PRIORITIES.md`:** update items 101 and 102 in place. At most one new item.
- **Merge #109 when:**
  - CI is green;
  - Part 0 is complete;
  - Parts A.3 and B.1 are proved or have a precise obstruction;
  - Part C is proved or reduced to named external hypotheses stated by content;
  - every fixture matches or has its mismatch explained.

## Constraints

- `AGENTS.md` labels; names provisional; check `state/views/NAMING_AUDIT.md`.
- Consume legitimacy, the allocation and the BRIA algebra as landed on this branch. Change them only where Parts A, D.2 and E say to, with an old-to-new map.
- **No authority row enters the enforcer.**
- The agent's indifference in tainted worlds (concern 4) stays out of scope. Name points of contact only.
- Nothing is registered.
