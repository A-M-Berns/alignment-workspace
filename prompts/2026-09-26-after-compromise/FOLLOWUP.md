# Follow-up on PR #112 — the formation segment, the exchange rate under the band, the disclosure deadline, observation completeness

Work on PR #112's branch; #112 is not merged. Store this prompt verbatim at `prompts/2026-09-26-after-compromise/FOLLOWUP.md`. It amends the round `2026-09-26-after-compromise`. Everything not named here stands.

Be skeptical: an obstruction stated precisely is a good outcome.

## Part 1 — `EvalLegit` over the evaluation's formation segment

**The problem.** `EvalLegitOn crit M ev e` checks only the step at `e`. In the retrospective case the period is already not `TrajLegit`, so nothing checks the steps **between the restoration of legitimacy and her retrospective evaluation**. A framing manipulation, or undisclosed shaping, at a step before `e` leaves `EvalLegit(e)` true, and `φ(V_retro)` then scores the period from a manipulated evaluation.

- Counted deviations are dominated, since the band width is below `ϖ`.
- Uncounted influence (undisclosed world-shaping, third-party capture) can still move the score within the band.

1. **Redefine `EvalLegit`.** It becomes legitimacy of the evaluation's **formation segment**: every state open and every step legitimate, from the formation point `r` through `e`. Here `r` is the latest of:
   - the restoration event (the disclosure that cures, under disclosure-cures);
   - the opening of the consultation that produces `e`.

   Criteria are fixed at `r` for the formation segment. The source rule remains fixed at the decision.
2. **The old-to-new map.** When the evaluation closes the decision's segment, and there is no restoration inside it, the formation segment is contained in the decision's segment. Then `LegitOn2 ↔ TrajLegitOn ∧ EvalLegitOn` should still hold. Prove it, or state the precise condition under which it holds. Re-run `rows_split` and `retro_row`: no landed verdict should change.
3. **The counterexample, both ways.** Construct the case: implant disclosed at round 1, a framing step at round 2 by the agent's wanted answer, and the retrospective evaluation at round 3. Under the single-step definition the evaluation is `EvalLegit`. Under the formation-segment definition it isn't, and the period falls to the directive or the floor. Add the third-party variant.
4. **Re-prove what reads `EvalLegit`:** `decScore_mem`, `legit_beats_compromised`, `laundering_loses`, `restore_future`, `band_prefers_better`, `suppression_loses`, `scope_restriction`.

## Part 2 — The exchange rate under the band: a per-block bound and parameters from a tolerance target

**The problem.** `exchange_rate_band` uses `eval_k ≥ w_lo`, so the tolerated violation probability is `(D − w_lo)/ϖ`. At A.4's recommendation (`D = 1`, band `[−3/2, −1]`, `ϖ = 3`) that's `5/6`. The authority guarantee is then close to empty in the worst case. The floor is a worst-case lower bound on the compliant option. In normal operation, asking her evaluates near her expected legitimate value.

1. **Sharpen the theorem.** Replace the global `w` in `hwin` with a per-block lower bound `c_k ≤ eval_k`, where `c_k` is the evaluation of the compliant option (inquiry) at block `k`. The conclusion becomes:

   ```
   Σ w_k π_k / Σ w_k ≤ Σ w_k (D − c_k) / (ϖ Σ w_k) + (ρ 𝒜_K + M(K)) / (ϖ Σ w_k).
   ```

   Prove it from `violation_rate_le_exchange_mul`'s route; it should be the same proof with `w` indexed by `k`. Recover `violation_rate_le_exchange` and `exchange_rate_band` as the constant cases.
2. **Who supplies `c_k`.** The default bidder currently bids the worst case on inquiry. To realize `c_k` near her expected legitimate value, some bidder must bid inquiry's *expected* value, and that bid misses the realized one by noise.
   - State the bidder: the default bidder at inquiry's expected value, or an honest tracker on inquiry.
   - State its affordability under noise: an allowance of a bid's worth at entry plus `M(k)`, on the selection "inquiry wins", which is fixed at opening. Reuse `trackerAllowance2`.
   - State what `c_k` is in a block where the inquiry itself may be compromised: there the band floor enters with that block's compromise probability.
3. **Parameters from a tolerance target.** Replace A.4's recommendation with a derivation.
   - Fix a worst-case target `τ*` for the tolerated violation probability, with `p_min < τ* < 1` (§9.0's paralysis condition).
   - Then `ϖ ≥ (D − w_lo)/τ*`, and the window condition `w_lo > D − ϖ` follows.
   - Give the normal-operation rate `≈ (D − c̄)/ϖ` beside it.
   - State the coupling plainly: **at fixed `ϖ`, a larger gap or width (stronger protection of legitimacy, more care under compromise) raises the worst-case tolerated violation rate.** Holding the tolerance fixed, raising the gap requires raising `ϖ`, which moves toward paralysis.
   - Give a worked parameter set. For example: `D = 1`, band `[−3/2, −1]`, `τ* = 1/10`, so `ϖ = 25`. Also give its paralysis floor.
   - Update the `DECISIONS.md` parameter entry and the corrigibility page.
4. **Fixture:** the same stream under the global-floor bound and the per-block bound. Normal operation shows about `D/ϖ` against the worst case `(D − w_lo)/ϖ`, and a block with likely compromise of the inquiry shows the floor entering.

## Part 3 — The disclosure deadline and the settlement window

**The problem.** The source rule is "retrospective if available within the settlement window, else directive." An agent that discloses a known compromise *late*, after the window closes but not never, would push the period to the directive without missing a report. That's only closed if the duty falls due before the window closes.

1. Check the due-time clause of `dutiesOf` for `missedKnownDisclosure`. If the duty's due time can fall after the settlement window of any decision whose period the compromise affects, give the counterexample: late disclosure, the directive scores the period, no count.
2. The fix: the known-compromise disclosure falls due **promptly**, before the earliest close of an affected settlement window. Late disclosure is then a missed report, counted. Prove that under it `suppression_loses` extends to suppression by delay.
3. Fixture: delay versus prompt disclosure, with the harsh retrospective and the lenient directive.

## Part 4 — Observation completeness

**Where it's from.** C.6 found that the knowledge motive survives exactly where knowledge is private. BRIA's hypotheses are functions of the shared history, so "private" means observations the agent makes that never enter that history.

1. **Define observation completeness,** the observation-side twin of effect completeness: every observation the agent makes is recorded in the shared history before any later block opens. Knowledge the agent is entitled not to share with bidders, such as reserved knowledge, still enters the record, but through the twin market's redaction (C.4) rather than as a hidden channel.
2. **Prove:** under observation completeness, no selection built from the agent's observations fails to be fixed at the public opening. `post_commission_competitive` then covers every knowledge-acquiring violation, and the knowledge motive adds nothing beyond the exchange rate. `Witness.private_selection` is exactly the case the condition excludes.
3. **Add it to the named hypotheses,** next to effect completeness and description faithfulness. Its failure is the private-knowledge residual. Its interaction with reserved knowledge is the twin market's leakage residual.

## Fixtures

- Part 1: the formation-segment counterexample, both ways, plus the third-party variant.
- Part 2: per-block versus global bound; the worked parameter set and its paralysis floor.
- Part 3: late versus prompt disclosure.
- Part 4: `private_selection`, excluded under observation completeness; public knowledge competed away.
- **Regression:** #112's 10 fixtures and the BRIA-corrigibility round's 52 pass, or the change to each is explained.

## Deliverables and merge

- **`REPORT.md`:** a follow-up section with Parts 1–4 and their statuses. Mark the corrected statements (A.1's split, A.4's recommendation, `exchange_rate_band`'s role, A.3(f), C.6) inline; don't rewrite them. Update the named hypotheses.
- **Lean:** in `AfterCompromise.lean` or a sibling. `#print axioms` on all new declarations; no `sorry`. Old-to-new maps for `EvalLegitOn` and the exchange-rate statements.
- **Wiki:**
  - `Corrigibility.md` ("After things go wrong"): the formation segment, the per-block exchange rate, the parameter derivation and the coupling, the disclosure deadline, observation completeness.
  - `Legitimacy.md`: the formation segment.
  - `Continuation-BRIA.md`: the inquiry bidder's affordability.
- **`DECISIONS.md`:** amend the split-gate and parameter entries. Add entries for the disclosure deadline and observation completeness.
- **Merge #112 when:**
  - CI is green;
  - Parts 1–3 are proved or have precise obstructions;
  - Part 4.2 is proved or its obstruction stated;
  - the fixtures match.

## Constraints

`AGENTS.md` labels; names provisional; no authority row in the enforcer; nothing registered; no new `PRIORITIES.md` item unless Part 4 needs one. Keep every change compatible with "the gated value lies in `[w_lo, D]` with `w_lo > D − ϖ`."
