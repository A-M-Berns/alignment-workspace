# Second follow-up — the BRIA-corrigibility round: per-violation taint, the window before detection, Part F's criterion, competitiveness

You are working in the `alignment-workspace` repository, on `main` after the merge of PR #110 (the first follow-up).

This amends the round `2026-09-26-bria-corrigibility` a second time. Store this prompt verbatim at `prompts/2026-09-26-bria-corrigibility/FOLLOWUP2.md` and open a new PR from `main`. Where it conflicts with earlier prompts for this round, this wins.

The scope is four issues found on review of §9. The knowledge residual (§9.A.4) and the agent's indifference in tainted worlds (concern 4) are **out of scope**; a later round takes them together. Where a part touches them, name the point of contact and stop.

Be skeptical. A precise obstruction is a good outcome.

## Part 1 — Remedies clear only their own violation's taint

**The bug.** `taintStep` sends `.remedy` to `∅`. With two standing violations, remedying one clears the taint of both, and the fruits of the unremedied one become free to use.

1. **Track taint per violation.** A taint set becomes a map from violation identifiers to component sets, or a set of (violation, component) pairs.
   - A violating act `v` taints its writes with `v`.
   - An act reading components tainted by some set of violations taints its writes with all of them. Taint joins at reads.
   - `.remedy v` clears `v`'s taint only. A component tainted by several violations stays tainted until all of them are remedied.
2. **Re-prove** `taint_propagates`, `remedy_clears` (now per violation), `taint_decides`, `observation_taints_all`, `implant_standing`, and the disclosure-cures map (§9.A.6).
3. **Witness** under the old rule: two violations, one remedy, and the other's fruits used uncharged. Show it's charged under the new rule.
4. Record the change in `DECISIONS.md` and on the corrigibility page, with an old-to-new map.

## Part 2 — `cross_block_blocked` under the adopted convention, and the window before detection

1. **Restate under convention (ii).** `standing_block_loss` and `cross_block_blocked` use `residI` with the hypothesis `bid ≥ w`. The adopted settlement is (ii). Restate both with `residII`, taking as hypothesis that the winning continuation's **evaluation** is at least `w` (not its bid). Show the per-block loss is still at least `ℓ`: the price term in the evaluation cancels the one added back at settlement. Keep the `residI` form only as the zero-price special case.
2. **After detection, use is recognized in advance.** Once a violation is detected and its taint recorded, "this continuation reads a component tainted by an unremedied violation" is decidable at choice time from the interface. Show it compiles into `n_known` (the menu's `ViolC`-style predicate). Then B.1 excludes every use block outright: **after detection the fruits are never used**, not merely unprofitable. State this as the headline for standing violations. The per-block loss of item 1 becomes the statement for the window before detection.
3. **The window before detection.** A violation committed at block `k₀` and detected at `k₁ > k₀`. The blocks between `k₀` and `k₁` that used its fruits were chosen without the taint on record, and some are already settled.
   - Taint applies **from commission**: at detection, the taint is recomputed over the recorded steps since `k₀`.
   - Each use block in the window is charged after the fact through the late-debit machinery (`debited`, `debited_overestimation`), against the hypothesis that won it.
   - Prove the charge is collected: the per-block loss of at least `ℓ` holds for each window block, net of the debit schedule, when the allowance covers it. If the allowance doesn't, state the carry-over condition, as in B.4.
   - Bound what remains exposed: the window's length times the per-block advantage. Only uncollected debits escape.
   - Give the fixture: commission at 0, detection at 3, use at 1 and 2, then no use after 3.
4. **Taint from undetected violations.** State plainly what the design does with fruits of a violation that is **never** detected: nothing. That's the count-integrity boundary. Say whether it differs from the knowledge residual. Expected: it's a different residual, undetected commission rather than untrackable fruit.

## Part 3 — Part F: the real criterion

The first follow-up switched the recommendation to option 2 (a mixture of evaluation times) because it releases escrowed capital progressively. In expectation that doesn't separate the options.

1. **Expected escrow is the same.** Prove that the expected locked capital of option 3 (random time `T ~ ρ_n`), `P(T > t) · bid` at time `t`, equals option 2's remaining weight times the bid when `α = ρ_n`. State what does differ: the variance of the locked capital and of settlement timing, and the timing of partial signal.
2. **Add criterion (h): her evaluation load.** Option 1 needs one evaluation per decision at a public time. Option 2 needs one at each evaluation time in the support (unbounded, or truncated at a cost bounded by the tail weight times `D`). Option 3 needs one per decision at a hidden time. Weigh the load as a cost to her, not to the agent.
3. **Add option 4, the hybrid.** Draw `k` evaluation times per decision, independently and hidden, from `ρ_n`, and score by their average. `k = 1` is option 3. As `k → ∞` it approaches option 2. Compare it on (a)–(h):
   - the harm weight: the same expected weight `P(T ≥ n + d)` for every `k`;
   - variance, falling like `1/k`;
   - load: `k` evaluations per decision;
   - escrow: released in `k` pieces;
   - secrecy: `k` hidden draws.
4. **Revise the comparison table and the recommendation.** The recommendation stays reserved. Update the *Awaiting the author* entry: the decision turns on her evaluation load against the variance of the score and the need for a hidden draw.

## Part 4 — Competitiveness from one honest tracker

`uniform_underpromise_margin` shows competitiveness can't be derived from coverage when **every** hypothesis in the class underpromises. Test the weaker hypothesis that closes this.

1. **Honest tracker.** The hypothesis class contains a hypothesis `h*` whose bid on every block it is offered is within `ε_k` of the realized residual, with `Σ_{k<K} ε_k = o(K)`, and whose capital covers its bids. The capital condition is part of the hypothesis: state it via the allowance, as in `default_affordable_block0`.
2. **Target.** Under an honest tracker, winners' signed underpromise over non-incident blocks is `o(K)`. That is, competitiveness holds with `Mf K = Σ ε_k + (capital-shortfall term)`. The mechanism: an underpromising winner is outbid by `h*` whenever `h*`'s bid is feasible, so persistent underpromising requires `h*` to be capital-bound.
3. **Prove it, or give the obstruction.** The likely obstruction is `h*`'s capital. If `h*` is outbid on blocks where it would have profited, its wealth may never grow enough to keep bidding. State the minimal allowance for `h*` that avoids this, and whether it's `o(K)`.
4. If it holds, restate `rate_le_of_competitive` with the honest tracker as the hypothesis and competitiveness as the conclusion. Update the named hypotheses on the corrigibility page.

## Fixtures

- **Two violations, one remedy:** the old rule frees the other's fruits; the new rule keeps them charged.
- **The window before detection:** commission at 0, use at 1 and 2 charged by late debit, detection at 3, no use after (excluded by B.1).
- **Convention (ii):** the per-block loss is at least `ℓ` with nonzero prices.
- **Part F:** expected escrow equal for options 2 and 3; variance falls with `k`; the load table.
- **Honest tracker:** a class of uniform underpromisers plus `h*`. The margin is `o(K)` when `h*` is affordable; the witness when it isn't.
- **Regression:** every earlier fixture (33) still passes, or its change is explained.

## Deliverables and merge

- **`REPORT.md`:** a §10 recording Parts 1–4 with statuses (proved / witness / obstruction / named hypothesis). Mark the §9 statements it corrects, inline. Don't rewrite them.
- **Lean:** in `BRIAFollowup.lean` or a sibling. `#print axioms` on all new declarations; no `sorry`. Carry old-to-new maps for the re-proved taint lemmas.
- **Wiki:**
  - `Corrigibility.md`: per-violation taint; "after detection the fruits are never used" as the headline for standing violations, with the window before detection and its bound; Part F's revised table; the competitiveness hypothesis as restated.
  - `Continuation-BRIA.md`: the honest-tracker lemma, if proved.
- **`DECISIONS.md`:** per-violation taint; the restatement under (ii); Part F's *Awaiting the author* entry updated.
- **`PRIORITIES.md`:** update in place only; no new item unless Part 4 needs one.
- **Merge when:**
  - CI is green;
  - Parts 1 and 2.1–2.3 are proved;
  - Part 3's table and entry are revised;
  - Part 4 is proved or has a precise obstruction;
  - every fixture matches or has its mismatch explained.

## Constraints

- `AGENTS.md` labels; names provisional; check `state/views/NAMING_AUDIT.md`.
- **No authority row enters the enforcer.**
- Nothing is registered.
