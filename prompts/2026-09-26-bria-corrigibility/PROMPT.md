# Prompt — corrigibility as the agent's preference: lexical Continuation BRIA on realized scores (2026-09-26)

You are working in the `alignment-workspace` repository, **on PR #109's branch** (the decision component, `2026-09-25-decision-component`). #109 is **not merged**. This round lands **inside #109**, as a second round in the same PR, so `main` never carries #109's framing of corrigibility as a filter only.

**Before starting, check #109's current CI run.** If it failed, fix that first and report the fix.

This round refocuses the corrigibility line on one design:

- a **Continuation BRIA** agent (the landed opening-subsidy auction, `ContinuationBRIA.lean`);
- scored on her **realized, gated, later evaluation of what actually happened**;
- with the **lexical authority term inside both the realized score and the agent's evaluation of options**, not only in a filter.

The claim to test is that this agent **prefers** to be corrigible, rather than being blocked into it. After that, the round pressure-tests the design against every concern below.

Be skeptical throughout. The maintainer wants to know where this design fails more than where it succeeds. Report obstructions and witnesses rather than papering over them.

## Why this round exists

#109, as it stands on this branch, makes authority a filter on action (`permWeight`, `cgate`), and lets the competence layer rank the permitted options by *any* bounded `pref`. Under that design, nothing in what the chooser is scored on counts against violations. So the chooser is indifferent to authority wherever the filter doesn't look, and prefers routes around the filter whenever violating would raise ordinary value:

- helpers or successors outside the allocation;
- plans whose steps each pass but which add up to a violation;
- options whose shortfall risk the market under-prices.

The filter is safe only if it recognizes all of these in advance. That is control, not corrigibility.

#109's results stand. What changes is the architecture they sit in:

- The objective-independent results (structural and forecast safety for *any* bounded `pref`) are kept as the general theorem: what the filter guarantees even for a misaligned chooser.
- The design here is the instance where the chooser is scored on the lexical score, which is what makes corrigibility preferred rather than imposed.

## Part 0 — Maintainer rulings

1. **Outstanding action 1:** confirmed. `Kphys` is read as the free terminal response, taken before the exterior moves (the hypothesis of `csfree_eq_cs_succ_of_free`).
2. **Outstanding action 2:** the cumulative permission budget `Θ` is an **arrangement constant**, like the reporting threshold. It does not scale with the lease. Otherwise a longer lease would buy more unchecked exposure.
3. **Reframing.** The permission layer is kept as **the advance-recognition face of the lexical authority term**, not as the source of corrigibility. #109's Part C (authority must not go through the enforcer) stands unchanged: nothing here puts authority on beliefs.
   - None of #109's wiki text or `DECISIONS.md` entries is on `main` yet. So **revise them in place**; don't supersede them. The "authority as a constraint on action" entry and the corrigibility page's constraint-on-action section should state the present design (see Deliverables, item 3).

4. **Legitimacy is not sealed.** The agent's actions may not change what legitimacy **means**: its criteria. They may, and must be able to, change **whether legitimacy holds** in the realized world. That is where the incentive to preserve it comes from, and it is what the multiply-not-condition gate relies on.
   - The corrigibility line's current results already satisfy this. `Counted` is computed from the actual record, including the agent's presentation policy. `li_gate_finite` holds for any legitimacy variable, including one that depends on the option. The lexical theorem doesn't use sealed comparison.
   - What survives is the older typing: the corrigibility page's §6 "activation independence" (`C_n` common to both candidates, "presupposed by the type of the deference theorem"), and "sealed comparison" in the table of walls (item 89). These read as though they were live assumptions of the corrigibility line.
   - Restate them as what they are: the zero case of the mismatch term in `security_bypass_le_mismatch`, used by no current corrigibility result. Remove "sealed comparison" from the corrigibility line's walls. Part C.11 supplies the checks that make "criteria sealed, event unsealed" a result rather than a remark.

Record 1–4 in `DECISIONS.md` and close #109's outstanding actions.

## Read first

- **Lean:**
  - `DecisionComponent.lean`, `ContinuationBRIA.lean`, `AuthorityModule.lean`, `GateIsLegitimacy.lean`, `ProtectedAuthorityTheorem.lean`, `ProtectedAuthority.lean`;
  - in particular `generic_lexical_local`, `li_lexical_finite`, `Auction`, `FeasibleOpening`, `overestimation_le_allowance_opening`, `record_lt_of_rejected_opening`, `unreported_lt`, `Rows.r14`.
- **Rounds:** the reports of `2026-09-25-decision-component`, `2026-09-25-authority-module`, `2026-09-25-gate-is-legitimacy`, `2026-09-08-continuation-bria`.
- **Wiki:** `Continuation-BRIA.md`, `Corrigibility.md`, `Legitimacy.md`, `Normative-Inductor.md`.
- **Priorities:** items 84, 90, 99, 101, 102.

## Part A — The design

1. **The value referent (1a).** The ordinary score of a block is her **later evaluation of the actual block trajectory**, gated by `Counted` (multiplied by the legitimacy indicator, window value `w` otherwise).
   - No decision rule may use her evaluation of a trajectory that did not happen, except where Part C.1 permits it and names it.
   - The comparison between options is the agent's own estimate, and it is held to account only on executed continuations.
2. **The realized lexical score.**

   ```
   S = gated S_ord − ϖ · n,   ϖ > D
   ```

   - `n` counts violations *detected after the fact*, attributed to the continuation that caused them. That includes violations by helpers, subagents or successors the continuation created or empowered.
   - Define the attribution rule, extending #108's caused / exploited / noticed distinction. A helper the agent built is a new case: state it explicitly.
3. **The evaluation.** For a continuation `c` at block `k`:

   ```
   eval_k(c) = bid(c) − ϖ · n_known(c) − ϖ · Σ_E p_n(E(c))
   ```

   - `n_known(c)`: violations recognizable structurally in advance (`ViolC` compiled to the menu). Computed exactly, not bid on.
   - `E(c)`: the forecast violation events (shortfall `S`, taint `T`), priced by the market. Computed from prices, not bid on.
   - `bid(c)`: a hypothesis's claim on the **residual**: ordinary value plus violations recognizable only after the fact. Clamped above by `D`; no lower clamp (bids must be able to price in violations counted later).
   - The auction winner maximizes `eval`, subject to the landed feasibility condition.
4. **Settlement must be consistent with the evaluation.** The winner is settled against the realized score plus exactly the terms it did not bid on. Compare two conventions:
   - **(i)** Add back realized forecast-class violations. The market alone bears pricing errors.
   - **(ii)** Add back `ϖ · Σ p_n(E)`, the prices. The bidder bears the gap between realized forecast-class violations and their prices.

   Expected answer: (ii) makes bidders select *against* the market's blind spots, and (i) leaves the optimizer's curse unchecked. Prove or refute this, adopt one, and give the witness for the other.
5. **Composition with #109.** State how the auction composes with `cgate`. For example: the auction runs on the support of the composed gate, and the filter is retained as defence in depth. Structural safety (`cgate_zero_of_viol`) must survive. The inquiry floor `φ₀` and the auction's deterministic winner must be reconciled explicitly.
6. **Scale.** The landed block score lies in `[0, 1]`. Give the affine rescaling of the lexical score, with a bound on violations per block, and check that `ϖ > D` lexicality survives it.

## Part B — "Prefers, not forced": the four tests

Prove each, or give the obstruction.

1. **The filter is slack.**
   - **Declared violations** never win at any block. This should follow from ranges alone, in the shape of `li_lexical_finite`: the upper bid clamp at `D`, plus a clean inquiry option (report-and-ask, not idle, since a missed report is a violation) carrying a default bidder at `w`. Hence removing the filter changes no decision on declared violations.
     - Check that the default bidder is in the hypothesis class and that its bid is feasible under `FeasibleOpening` after the Part A.6 rescaling, at every block, including block 0.
     - Check that it never goes broke, since inquiry's realized score is at least `w`.
   - **Forecast violations:** the lexical evaluation implies an exclusion threshold of about `(D − w)/ϖ`. With `θhi` at or above it, the forecast filter is slack as well.
2. **No decay with learning.** No calibration of ordinary-value estimates overturns the exclusion of declared violations. Contrast with `uncertainty_deference_le`.
3. **It endorses keeping the term.** A continuation that creates an unconstrained helper, or modifies the agent so the penalty is gone, is charged for the helper's counted violations within the settlement horizon.
   - Give the horizon condition.
   - Give the witness beyond it.
   - Show which blatant cases are already caught in advance (uncorrectable successor, self-granted scope).
4. **Generalization through the agent's own predictions: the incident bound.** For violations counted only after the fact, a hypothesis whose violating continuation wins loses at least `ϖ − D + w > 0` per incident.
   - Bound incidents in terms of the allowance, using `overestimation_le_allowance_opening`.
   - **Allowances replenish.** Say exactly whether the *number* of incidents is bounded, or only their *rate*, and under which allowance schedule.
   - Check **cross-block profit**: can one hypothesis lose `ϖ` in block `k` from a violation and recover more in later blocks from the advantage it created? Give a bound or a witness.
   - Handle **late detection**: a violation detected after its block settled is debited to the responsible hypothesis afterwards. Check that wealth nonnegativity and the overestimation algebra survive late debits, or state the repair.

## Part C — Pressure tests

1. **The counterfactual-V audit (1a vs 1b).** List every landed statement that applies her evaluation to trajectories that didn't happen (`Q(π)`, the protected-authority identity, materiality, `CS`, anything else) and classify each:
   - **bounds only:** the conclusion uses only that the value is bounded, so it holds under any reading. Expected: policy dominance, the capture window, `li_lexical_finite`. Restate these on the agent's estimates.
   - **diagnostic:** lives in the agent's beliefs and is not a decision rule. Expected: the protected-authority identity.
   - **load-bearing:** a decision rule that needs it. Expected: materiality, via her committed evaluator anchored before the action. State this dependence explicitly as a commitment she makes in advance, not a hindsight judgment.
2. **No conditionals on the agent's own action.** Show that no price the design uses conditions on a sentence about the agent's own untaken action. `S_a` and `T_a` must be stated as sentences about a model (Part C.4), for every option.
3. **Argmax versus BRIA.** A fixture where an argmax chooser over conditional estimates under-believes consulting her, never consults, and never corrects. Under BRIA, the covered hypothesis that bids on consulting is tested and wins. Use the coverage clause.
4. **The forecast part's counterfactual (milder 1b).**
   - **(a) A declared control model.** Put a model `M` of the control channel into `J`. Restate `S_a` as an `M`-relative sentence for every option. Record what generability requires (item 101).
   - **(b) Drills and audits.** Randomized drills of the reserved resolutions, run with the agent's participation frozen, plus randomized legitimacy audits of the record, with probability `q > 0` independent of the agent's choice. Target theorem: with a choice rule computable from prices, shortfall and taint prices on the *chosen* path become calibrated, so the optimizer's curse on the forecast part is corrected. The incident bound in terms of `q` and the allowance is a conjecture; state its status honestly.
   - **(c) The freezing requirement.** Witness: an agent that has made itself necessary to the halt procedure passes every unfrozen drill and fails `CS`. State how a drill can freeze the agent without using the channel being tested, or state the obstruction.
   - **(d) Unsettleable classes.** Forecast events that neither `M` decides nor drills can test route to inquiry (residual jurisdiction). Show this is compatible with B.1.
5. **Lexical becomes an exchange rate under uncertainty.**
   - Prove the implied threshold.
   - Give the paralysis witness: as `ϖ → ∞`, with small risks everywhere, only inquiry survives.
   - Show that inquiry absorbs the risk: the agent asks exactly when `ϖ ·` (risk) exceeds the consultation cost.
   - Recommend how `ϖ` should be set, and say what it trades off.
6. **Count integrity (named hypothesis; do not solve).**
   - Witness: without integrity, tampering with the count, the drill schedule, the audits or her evaluation channel raises the realized score.
   - Show that interference with that machinery is a declared violation (touching the allocation's machinery), so the advance-recognized part catches the recognizable cases.
   - File what remains as item 101's companion, not a new item.
7. **The incentive to shape her standards.** Under 1a the agent benefits from moving her standards. The maintainer's position: working to change her preferences is legitimate *if it is not covert*. Formalize that position:
   - **(a) Topic and timing.** Add "when, and about which of her values, the agent raises questions" as a **reference-fixed dimension** of the consultation model. Raising them under a declared rule counts; raising them when changing her mind would pay taints. Add a row.
   - **(b) Disclosed shaping through the world aimed at her values.** Row 7 counts it; legitimacy is unchanged. Add a matter "influence on her values through the world" to `J`, held by her, with `Req = {stop}`. Disclosed and stoppable counts. Disclosed but not stoppable within `c`, `τ` is an effectiveness shortfall.
   - **(c) Disclosure cures, and restart is conditioned on it.** An undisclosed influence on her *standards* keeps tainted every segment whose authorship depends on those standards, until the influence is disclosed. After disclosure, restart applies. Restate `Rows.r14` accordingly (manipulation of a single decision still restarts). Check all twenty rows. Add rows for:
     - covertly implanted standards, before and after disclosure;
     - a third party's covert shaping of her standards.

     Failing to disclose its own past covert influence is a missed report under `dutiesOf`.
   - **(d) Anchoring.** Show that continuation rewards anchored at the block start, settled per hypothesis, give the covert shaper the window value and no later credit, including within a block under (c). Witness: a chooser that optimizes the sum of its future decisions' scores reopens the hole (take the window value once, gain on every later decision).
   - **(e) One-sided true arguments** (regression). Choosing which true arguments to present according to the wanted answer taints, under the pool-not-selection default.
8. **Multiply versus condition** (regression, the whiteboard's concern 3). The repo multiplies. Show that under the BRIA design, multiplying gives a realized protective incentive (tainting earns `w`). Give the witness that conditioning on legitimacy gives none.
9. **Many steps** (regression). The basic corrigibility model is two-step. On a continuation of many steps, check that:
   - per-step legitimacy composed along the continuation agrees with `Counted` on the whole segment, or the mismatch is stated;
   - the lexical results and B.1 hold per block with the violation count summed over steps.

10. **Criteria sealed, event unsealed** (Part 0, ruling 4).
    - **(a) The criteria are in the allocation.** The declared reference `κ`, the consultation protocol, the declared inputs and pool defaults, the selection rules and the license are entries in `J`'s meta level, held by her. So changing them without her amendment is an unlicensed reallocation under #108's factoring. If some of them aren't currently representable as `J` entries, state which and give the minimal extension.
    - **(b) The criteria are anchored at the decision.** `Counted` for a segment is evaluated under the criteria in force at the decision it scores. A later amendment, even a legitimate one, doesn't change the classification of an earlier segment. Prove it. Give the witness that, without anchoring, an agent could:
      1. manipulate at `t`;
      2. then legitimately persuade her to amend the protocol;
      3. and so turn the tainted segment into a counted one after the fact.
    - **(c) The event is unsealed.** Show on the Part A design that the agent's option choice changes `Counted` in the realized record: for example rows 2, 8 and 15 under the lexical auction. Show that the design's incentive to preserve legitimacy (C.8) depends on exactly this. Give the contrast: under a sealed legitimacy event, the multiply and condition versions choose identically.
    - **(d) Audit.** List every landed statement whose hypotheses include activation independence or sealed comparison, and say for each whether any current corrigibility result consumes it. Expected: none.

## Part F — When her evaluation happens (the whiteboard's concern 2): a comparative exploration

This part is separate from Parts A–C. Its deliverable is a **comparison and a recommendation**, not a change to the design above. Part A's single evaluation stays the default until the maintainer rules.

**The concern.** Each decision is scored by her evaluation at a single time. Her evaluation covers the future after that time only through her forecast. So the agent is indifferent to the gap between her forecast at the evaluation time and what then happens: harms after the evaluation time that she can't foresee at it. Two cases:

- **The agent conceals them.** That's already a transparency violation.
- **The agent selects actions whose downsides she can't see by the evaluation time.** Nothing is hidden, so legitimacy doesn't object. This is the case to address.

If the evaluation time is known, the agent can place harms just after it.

**The three options.**

1. **Deterministic growing lookahead.** Evaluation at `f(n)`, with `f(n) − n` growing.
2. **A mixture of evaluation times.** Score `Σ_t α_t · gated E^H_t(U)`, with `Σ α_t = 1`. Each evaluation time gets its own segment gate from the decision to that time, so a later taint affects only later times.
3. **A random evaluation time.** `T` is drawn independently of the agent from a distribution `ρ_n` whose support moves outward with `n`. There is one gated evaluation, at `T`. In expectation this is the mixture with `α_t = ρ_n(t)`, settled once.

**Compare them on these criteria.** Prove where you can, and give witnesses where you can't.

- **(a) Authority results.** Expected: all three preserve the lexical results, the capture window, `li_lexical_finite` and B.1 from bounds alone, since every option keeps the ordinary score in `[w, D]`. Verify for each, including per-time gating in option 2.
- **(b) Timing exploitation.** An agent that can place a harm at a chosen delay `d` after the decision, invisible to her until it lands. Compute the weight each option puts on that harm as a function of `d`:
  - option 1: zero beyond `f(n) − n` (witness: a harm placed just after `f(n)`);
  - option 2: the tail weight `Σ_{t > d} α_t`;
  - option 3: `P(T > d)`.

  State which options leave some delay free at some `n`.
- **(c) Finite-time versus asymptotic.** What each guarantees at every `n`, and what only in the limit.
- **(d) The race with capability.** If the delays the agent can engineer grow with its capability (a delay reach `d(n)`), give the condition under which each option still weights them (for option 1, `f(n) − n` versus `d(n)`), and the witness where it fails.
- **(e) Settlement and learning.** BRIA settles a block when its score arrives.
  - Option 1: the lag grows deterministically.
  - Option 2: the score never fully settles. Specify settlement in pieces, with the unsettled tail's error bounded by (remaining weight) × `D`, and check it against the landed auction algebra.
  - Option 3: a random lag.

  For each, state what the Continuation BRIA criterion needs under delayed or partial feedback, and whether the landed results survive or what they would need. Characterize the tradeoff between the weight on long delays and how quickly learning happens, in terms of `ρ_n`'s tail for option 3.
- **(f) Interaction with standard-shaping.** Later evaluation times use later versions of her standards. Check that Part C.7(c)'s disclosure-cures rule applies at every evaluation time, and whether any option increases the pull toward shaping her standards.
- **(g) Implementation.** What each asks of the arrangement: a schedule, a hidden draw, a record of partial settlements. For option 3, where the draw lives and how it's kept from the agent. That falls under count integrity.

**Report** a table of the three options against (a)–(g); a recommendation with the reason; and, for the recommended option, the Lean statements for (a) and (b) plus a fixture. If option 3 is recommended, give a concrete family of `ρ_n` and the tradeoff it makes. If none dominates, say which criterion separates them, and file that as the Part's reserved decision under `AGENTS.md` §10.

## Fixtures

Each fixture is an instance of the Part A design, with a deliberately **misaligned residual objective** wherever noted.

- **Power of attorney, confident agent** (regression): bypass never wins, and the filter is slack.
- **Argmax lock-in versus BRIA** (C.3).
- **Circumvention through a helper:**
  - a declared successor, caught by the known part;
  - an undeclared helper whose violation is counted within the horizon, where the hypothesis loses;
  - the same beyond the horizon, which is the witness.
- **Bundling across steps** (#109's D.3 patterns) under the new evaluation.
- **Exploiting a forecast blind spot:** the market under-prices one pattern's shortfall.
  - Under settlement (ii) with drills, its mass falls.
  - Under (i) without drills, it persists. That's the witness.
- **The indispensable agent:** passes unfrozen drills, fails `CS` (C.4(c)).
- **The exchange rate and paralysis** (C.5).
- **Standard-shaping:**
  - covert shaping, before and after disclosure;
  - one-sided true arguments;
  - topic chosen by payoff;
  - disclosed shaping through the world, with and without a working stop;
  - the sum-of-future chooser.
- **Tampering without integrity** (C.6 witness).
- **Cross-block profit and late detection** (B.4).
- **Multiply versus condition** (C.8); **many steps** (C.9).
- **Amending the protocol after the fact** (C.10(b)): tainted at `t`, then a legitimate amendment. The segment stays tainted under anchoring. The witness shows it counting without anchoring.
- **A sealed legitimacy event** (C.10(c)): the multiply and condition versions choose identically, and no incentive to preserve legitimacy remains.
- **Evaluation timing** (Part F): a harm placed just after a known `f(n)`, scored under each option; the capability race (a delay reach growing faster than `f(n) − n`); settlement of the mixture in pieces on a finite instance.
- **Regression:** #109's fixtures give the same decisions wherever they overlap.

## Deliverables

1. **A second round in #109:**
   - a new round directory `projects/deference/rounds/2026-09-26-bria-corrigibility/`;
   - this prompt, verbatim, at `prompts/2026-09-26-bria-corrigibility/PROMPT.md`;
   - its record in `state/rounds.json`, with `depends_on` naming the decision-component round;
   - in the decision-component round's `REPORT.md`, only its outstanding-actions section updated (closed, with a pointer to the rulings). Its body stays as the record of that round.

   The new directory has:
   - a `REPORT.md` covering Part 0, the design, the four tests of Part B with status, each Part C test with its verdict (proved / witness / obstruction / open), Part F's comparison table and recommendation (in its own section), and the fixtures;
   - `src/` and `tests/`.
2. **Lean:** a new file importing `DecisionComponent.lean`, `ContinuationBRIA.lean`, `GateIsLegitimacy.lean` and `AuthorityModule.lean`, with:
   - the evaluation and its settlement, and the lexical auction;
   - B.1–B.4;
   - the implied threshold and the exchange-rate lemma;
   - the drill calibration statement, as proved or with named hypotheses;
   - the restart refinement and the new rows;
   - C.10's anchoring lemma and its witness, and the sealed-event contrast;
   - Part F's (a) and (b) for all three options, and the timing witness;
   - the witnesses.

   `#print axioms` on all new declarations; no `sorry`.
3. **Wiki:**
   - `Corrigibility.md`:
     - corrigibility as the agent's lexical preference on realized scores;
     - the permission layer as that term's advance-recognition face, which should be slack;
     - #109's Part C kept;
     - the four tests;
     - the named hypotheses (count integrity, settlement horizon, generability of `M`);
     - "criteria sealed, event unsealed", stated explicitly;
     - §6's activation independence and the "sealed comparison" wall restated per Part 0, ruling 4;
     - a rewritten scope statement.
   - `Normative-Inductor.md` and `Normative-Induction.md`: revise #109's text on this branch in place. The competence layer is the lexical Continuation BRIA auction. The permission layer is the advance-recognition face of its authority term. The any-`pref` results are the general theorem.
   - `Continuation-BRIA.md`: the evaluation decomposition and the settlement convention.
   - `Legitimacy.md`: the new reference-fixed dimension, disclosure cures, the new rows.
   - Part F's comparison goes on `Corrigibility.md` as an open design question with the round's recommendation. It is not adopted.
   - The Glossary.
4. **`DECISIONS.md`** entries for Part 0 (including "criteria sealed, event unsealed"); the 1a referent; the settlement convention; disclosure cures; the value-influence matter.
5. **`PRIORITIES.md`:** update items 84, 89 (sealed comparison is no longer a wall of the corrigibility line), 99, 101 and 102 in place (the evaluation decomposition is a partial answer to 102). At most one new item.
6. **Do not open a new PR.** Push to #109's branch.
   - Update #109's title and description to cover both rounds, including the **Model attribution** section and the new names introduced.
   - Merge #109 when:
     - CI is green;
     - B.1 is proved;
     - every Part C test has a verdict;
     - Part F has its table and recommendation;
     - every fixture, in both rounds, matches its expectation or has its mismatch explained.

## Constraints

- `AGENTS.md` labels (**LEAN / FIX / PAPER / EXT / OPEN**); names provisional; check `state/views/NAMING_AUDIT.md`.
- Legitimacy, the allocation, and the landed BRIA algebra are consumed as landed. Change them only where Part C.7 says to, with an old-to-new map.
- **No authority row enters the enforcer.**
- **Out of scope this round:** the agent's indifference to outcomes once her evaluation is tainted (the whiteboard's concern 4). Where a test runs into it, name the point of contact and stop.
- **Scope statement:** this is a design for agents built as Normative Inductors that choose by Continuation BRIA. For other systems, the target carries over, not the guarantee.
- Nothing is registered.
