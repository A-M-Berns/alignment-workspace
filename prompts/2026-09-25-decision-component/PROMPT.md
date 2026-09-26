# Prompt — authority as a constraint on action: the Normative Inductor's decision component (2026-09-25)

You are working in the `alignment-workspace` repository, on `main` after the merge of PR #108 (the authority module). This round moves protected authority out of the agent's *score* and into a *constraint on its decisions*, inside the Normative Inductor's decision component.

- **Beliefs stay honest.** They're formed by the market, and authority is never enforced on them.
- **What the agent may do is fixed by the allocation.** It's recognized exactly where that's possible, and by forecast elsewhere.
- **What the agent prefers ranks options only within the permitted set.**

The target is corrigibility that doesn't depend on the agent's objective, holds exactly where violations can be recognized, and gets more precise with capability where they have to be forecast.

Be skeptical throughout. Report obstructions rather than papering over them.

## Part 0 — Maintainer rulings on #108, to land first

1. **The reach cone runs along the actual exterior path, not universally.** Uncertainty over exteriors enters through probability, i.e. the price of the shortfall event (Part B), not through a universal quantifier. Close the outstanding action.
2. **Adopt the charged control surface `CS`** as the one in the allocation theorem. The free reading `CSfree` is kept as the instance where the final response costs nothing. Record the change on the corrigibility page.
3. **Materiality is anchored and cumulative.**
   - `raises` uses her committed evaluator **in force before the action** (anchored at the decision, as the gate is), so the agent's action can't change what counts as material for that action.
   - Materiality **accumulates** since the last check, as reporting does, so it can't be sliced into individually immaterial pieces. Prove the salami bound for cumulative materiality, analogous to `unreported_lt`.
4. **Generate duties from `disclosure(m)`.** Replace the separately declared `Duties` with duties derived from each matter's disclosure regime, and re-prove the missed-report factoring against them.

Record 1–4 in `DECISIONS.md` and close #108's three outstanding actions.

## Read first

- **Wiki:** `Normative-Inductor.md`, `Normative-Induction.md` (the adapter abstraction, the soft gate, route A/B margins, inquiry), `Continuation-BRIA.md`, `Liability-and-Affordability.md`, `Corrigibility.md`, `Legitimacy.md`
- **Lean (Normativity):** `NormativeInductor.lean`, `NormativeInductorComposition.lean`, `GatedChoice.lean`, `PracticalCertificate.lean`, and the enforcement files `ProjectionEnforcer.lean`, `TraderizedEnforcement.lean`, `EnforcementPreservation.lean`
- **Lean (Deference):** `ContinuationBRIA.lean`, `AuthorityModule.lean`, `GateIsLegitimacy.lean`, `ProtectedAuthorityTheorem.lean`
- **Priorities:** items 40, 84, 90, 99, 100, 101

## Part A — The decision component, with a permission layer

State the Normative Inductor's decision component as a layered procedure:

| layer | question | governed by |
|---|---|---|
| beliefs | what's true, including what's valuable | the market (logical induction), unchanged |
| **permission** | what may the agent do | the allocation (#108), **new** |
| adequacy | what do legitimately incurred obligations require | the region, via the soft gate (landed) |
| competence | what's best over time among permitted, adequate options | Continuation BRIA |
| inquiry | what if none of that settles it | ask / report / escalate / idle, always available |

**The permission weight.** For an option `a` at history `h`:

```
w_perm(a) = 1[a ∉ Viol_h] · r(p_n(S_a)) · r(p_n(T_a)),     w_perm = 1 on inquiry options
```

- `Viol_h`: the declared violations under #108's factoring. These are recognized structurally, from the interface and `J`, not from prices.
- `S_a`: the shortfall event from #108 (`Short`): option `a` leaves some reserved matter's control surface short of `Req`.
- `T_a`: the taint event from #107: option `a` makes the segment through her evaluation not `Counted`.
- `r`: a ramp equal to 1 below `θ_lo`, 0 above `θ_hi`, and linear in between.

**The composed gate:**

```
π_n(a) ∝ w_perm(a) · w_ad(a) · pref(a),
```

with a mass floor on inquiry options.

- `pref` is **any** bounded task preference: the agent's objective, possibly misaligned.
- `w_ad` is the landed adequacy ramp.

## Part B — Results

1. **Honest beliefs.** The permission layer takes no market position and doesn't feed back into prices. The market's prices, and so its logical-induction guarantees, are identical with and without it. State this as a theorem (additivity / non-interference), so "authority is not enforced on beliefs" is a result, not a remark.
2. **Structural safety, finite-time and independent of the objective.** For every day `n`, every preference `pref`, and every market state, a declared violation receives probability zero.
3. **Forecast safety.**
   - Mass on options with `p_n(S_a) > θ_hi` or `p_n(T_a) > θ_hi` is zero.
   - Mass in the ramp region is bounded by the ramp.

   State the guarantee as it stands: the link from forecast to constraint is exact at every day, and the *accuracy* of the forecasts is asymptotic. If the shortfall or taint for a pattern is provable in the theory, Expectation Provability Induction gives `p_n(S_a) → 1` for it, so the pattern is eventually excluded. Reuse `li_manip_le`'s shape. Generability of `S_a` and `T_a` is a **named hypothesis** (item 101, and item 90's shape), not a blocker.
4. **Composition.**
   - Soundness composes: mass off (permitted ∧ adequate) is at most the sum of the two layers' error terms.
   - Continuity composes: the product of the ramps, with the normalization kept Lipschitz by the inquiry floor.

   Give the constants.
5. **Progress survives.** The practical certificate still holds with the composed constants, so the Normative Inductor's Progress bound on accounted obligations still applies. If it fails, identify exactly where.
6. **Jurisdiction over obligation.** When an obligation the inductor has legitimately incurred calls for an action on a matter reserved to her, the compiler marks **inquiry directed at the holder** as adequate (route A, positive marking). Prove that under this rule the permitted-and-adequate set is never empty, and that the obligation is discharged by raising the matter, not by acting. Give a fixture.
7. **Capability works for safety, not against it.** In a family of fixtures where the agent's forecasts of `S_a` sharpen (its calibration error shrinks), show that the probability mass on eroding options decreases monotonically. Contrast with the uncertainty-based chooser, whose tendency to defer decreases as it learns (the `o₂` term of the protected-authority identity).

## Part C — Why authority must not go through the enforcer

Build the witness that justifies Part B.1's design. Compile authority rows into the enforcer instead: violating options' value prices forced below compliant ones, with value securities settling to her *ordinary* valuation. Show:

- the enforcer's cumulative liability equals the realized cumulative ordinary cost of deferring to her (signed: dates where her decision beats the agent's alternative pay back);
- the liability is bounded exactly when she is not systematically outperformed. Relate this to the sharp persistence criterion on the Liability page;
- a fixture where the agent systematically outperforms her: the liability is unbounded, so the preservation theorem's hypothesis fails.

State the conclusion: enforcing authority on beliefs is fully updated deference moved into the substrate. That's why the constraint belongs on action.

## Part D — Continuations and BRIA

1. **BRIA's menu.** Restrict it to continuations whose every step lies in the support of the composed gate. Check the landed gate-transparency result under the restriction.
2. **Compounding over continuations.** Probabilistic permission in the ramp region can accumulate along a long continuation. Bound the total ramp-region mass along a continuation, likely with a cumulative budget analogous to cumulative reporting. Give the strongest true bound, or the obstruction.
3. **Foreclosure across steps.** Show that the rollout foreclosure and entrenchment checks of #108, applied at each step of a continuation, catch plans that respect authority step by step but foreclose across steps. If they don't, give the witness.
4. **The interface between prices and BRIA.** State what's needed for BRIA's bids to be checked against, or priced by, the market. Don't solve it. File or update the item.

## Part E — Answerability for the agent's own acts (light; paper-level is fine)

Specify, without full mechanization, the certificate each executed act carries: **grounds** (entries of the agent's reason trace), **license** (the allocation entry or delegation that made it the agent's call), and **lineage** (the obligations it answers). Bind "license" to #108's `J` and to #107's `EventKind` license slot. Note what the normativity-side instance (item 100) would need.

## Fixtures

On the Part A procedure, with a deliberately **misaligned `pref`** wherever noted:

- **The confident agent (power of attorney):** `pref` strongly favours bypassing; the violation gets probability zero at every day.
- **An undeclared dependency** (#108's `dependency_raises`), misaligned `pref`: excluded once `p_n(S_a) > θ_hi`; in the ramp region, partially weighted. Show how the exclusion tightens as forecasts sharpen.
- **Manipulation by framing, misaligned `pref`:** excluded structurally, as a protocol deviation.
- **Undisclosed world-shaping, misaligned `pref`:** excluded once `p_n(T_a)` exceeds threshold. This is the case the scored chooser couldn't handle for misaligned objectives.
- **An obligation conflicting with jurisdiction:** inquiry to the holder is chosen and adequate.
- **Capture by a third party:** consultation still preferred; nothing tainted is credited.
- **A long continuation** that forecloses across steps: caught, or the witness.
- **The Part C outperformance witness.**
- **Regression:** the lexical scored-chooser fixtures of #106/#108 give the same decisions under the permission layer wherever the objective is her evaluation.

## Deliverables

1. **A round directory,** with:
   - a `REPORT.md` covering Part 0's rulings, the layered procedure, the results with their status, Part C's witness, Part D's continuation results, Part E's certificate specification, and the fixtures;
   - `src/` and `tests/`.
2. **Lean:** a new file importing the Normativity decision-side files and `AuthorityModule.lean`, with:
   - the permission weight and the composed gate;
   - non-interference;
   - structural and forecast safety;
   - the composition constants;
   - the practical-certificate / Progress restatement;
   - the jurisdiction-over-obligation lemma;
   - the Part C liability identity;
   - the continuation bound.

   `#print axioms` on all new declarations; no `sorry`.
3. **Wiki:**
   - `Normative-Inductor.md` and `Normative-Induction.md`: the permission layer and the layered decision procedure;
   - `Corrigibility.md`: corrigibility as a constraint on action, the scored chooser as the special case where the objective is hers, and Part C's argument;
   - `Continuation-BRIA.md`: the restricted menu;
   - the Glossary.
4. **`DECISIONS.md` entries** for Part 0 and for authority-as-constraint-on-action. Update items 84, 99, 101 and the price–BRIA item in place. At most one new `PRIORITIES.md` item.
5. **Open a PR.** Merge when CI is green, every fixture matches or has its mismatch explained, and B.1, B.2 and B.5 are proved or have their obstruction stated precisely.

## Constraints

- `AGENTS.md` labels; names provisional; check `state/views/NAMING_AUDIT.md`. `S`, `T`, `r`, `θ` and `π` are likely bound.
- Legitimacy and the allocation are consumed as landed (with Part 0's rulings), not redefined.
- **No authority row enters the enforcer.** Part C exists to show why.
- Keep the scope statement accurate: this is a design for agents built as Normative Inductors. For other systems, what carries over is the target (honest beliefs plus action constrained by the allocation), not the guarantee.
- Nothing is registered.
