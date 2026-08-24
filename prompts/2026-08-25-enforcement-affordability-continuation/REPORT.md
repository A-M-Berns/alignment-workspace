# Report

**Attribution.** Prompt author: user, model not stated. Executor: Claude
Fable 5 (Anthropic). Dispatched and executed 2026-08-25. Worked from the
parent round's branch head `1042c8b` on
`round/2026-08-24-enforcement-affordability`.

**Verdict.** `THE ONE-COORDINATE THEOREM IS TRUE AND NEEDS A FOURTH
HYPOTHESIS THE PARENT ROUND DID NOT STATE.` C1's fork lands on the negative
side: the self-financing inequality does **not** close, and the
parameterized-chest fallback does not rescue it either, because a component
recycling the enforcer's own losses from an unconstrained coordinate refills
its chest faster than the chest draws down. C0 is therefore stated with an
explicit no-cross-coordinate-subsidy hypothesis, and each of its four
hypotheses carries a necessity witness.

The continuation extends the round at
`projects/normativity/rounds/2026-08-24-enforcement-affordability/`.
Nineteen new exact fixtures (`tests/test_continuation.py`), 46 in the round;
same model, same pinned inputs, both re-verified.

## Findings

1. **C1, channel (b) — other budgeted components.** Real and defeats the
   per-component reading: an attacker with budget 1 throughout, harvesting a
   patsy of budget 64 through an unconstrained settled sentence, drives
   liability to 11.74 against 8.50 for the T2 bound at its own war chest, and
   against 0.44 with the harvest off. Closed in the aggregate: liability stays
   inside `(b_A + b_B)·C + slack` at every budget tested. Recycling through
   this channel redistributes the war chest; it cannot mint.
2. **C1, channel (c) — the enforcer's own losses.** Does not close, and no
   schedule-local bound survives it. One component, budget 1, pumping a moving
   peg on `ψ` and spending an eighth of capital a day against a **static,
   perfectly-margined** peg on `φ`: chest, `φ` flow and `φ`-coordinate
   liability all compound geometrically over eight cycles (flow ratio 1.257 to
   1.270 per cycle, no decay), the component never shut off and never in
   breach of its floor. The `φ` peg satisfies every geometric hypothesis
   available and its liability is unbounded.
3. **The parameterized-chest form fails as stated.** Read off the realized
   drawdown at the throttling world it gives `W = 0.42` against liability
   21.91. The unconditionally true parameterization is by gross capacity —
   budget plus income received at the throttling world — which under channel
   (c) is itself unbounded, so the statement is true and empty. Reported as a
   fork rather than repaired; no fencing or budgeter modification was invented.
4. **The discriminator.** `κ = 0` exactly when the enforcement trader's
   cumulative value is nonnegative at the world that throttles the opposition.
   The projection trade takes the side opposite the flow, so on a static
   interior peg this holds structurally — asserted daily over a 22-day run —
   and it is precisely what the pumped schedule breaks, through the second
   coordinate.
5. **C0.** Stated with four hypotheses — containment, margin, stationary
   interior peg, no cross-coordinate subsidy — and bound
   `B ≤ W·C(lo,hi) + c·Σ2^-n` with `C ≤ (1−m)/m`, no term mentioning the
   tolerance. Eight-step proof sketch in skeleton notation, each step tagged
   with its fixture and its `Contrib` composition target. **Each of the four
   hypotheses has a necessity witness**: (H1) the parent's W1, (H2) the
   parent's near-vertex family, (H3) the parent's W3 pump, (H4) this
   continuation's pump-and-drain.
6. **Lean promotion is a market-side project.** Of C0's eight steps, exactly
   one (aggregation without netting) promotes today from existing `Contrib`
   lemmas. Two more are one lemma away. The remaining five — the MarketMaker
   day bound, the flow–inventory identity, the billing geometry, the allowance
   term, tolerance-freedom — have no `Contrib` counterpart at all, because
   `Contrib` models the budgeting side and none of the market side. The
   load-bearing gap is the flow–inventory identity, the only step that is
   neither convex geometry nor an instance of a floor lemma.
7. **C0′, the impossibility.** The parent's W1 promoted to a skeleton-facing
   proposition with an explicit efficiently-computable exploiter buying one
   share a day after settlement, cumulative value `≥ (μ/2)(N−n₀) − c₀` at
   every plausible world, hence exploitation and, by Theorem 4.4's
   contrapositive, unbounded liability for **any** enforcement trader
   realizing the schedule.
8. **C2.** Theorem D.1's agreement condition is shown load-bearing rather than
   bookkeeping, and checked directly by exhaustive enumeration over
   sub-supports: violated at every day on the alternating-singletons schedule,
   satisfied at every day on the nested settlement stream. The severance is
   restated with its own fixture — at least `1/8` banked per day, at least 2
   over sixteen days, while every horizon assessment stays within 1 of zero
   and liability inside `1 + Σ2^-n`.
9. **C3.** The biconditional holds. Absorption gives **exactly** zero at every
   flow size, both undecided and post-settlement; exclusion forces strictly
   positive liability in all twelve configurations, at `(inventory)·m` to
   within the slack. The floor `m²/4(1−m)` is uniform in the flow size, which
   is not an artifact: liability *decreases* in flow because a larger flow
   trips the throttle sooner.
10. **Spot-checks of the parent.** All pass. The parent's `lifetime_liability`
    reads the final-horizon deficit while Definition 4.1 takes the supremum
    over horizons, so the parent's bounds do not transfer by definition; they
    transfer in fact, because the two quantities are exactly equal on every
    parent fixture re-run and across a scan over region, flow, side and budget.
    No parent grade changes.

## Deviations

- **`README.md` was edited**, which the dispatch's "the parent's grades and
  text are not edited" would otherwise forbid. Its file list stated "27
  adversarial fixtures", which the continuation makes false. Corrected to 46
  with the new files listed; the parent's verdict paragraph is untouched. Flagged
  here because it is an edit to a parent file rather than an extension of one.
- **The C2 non-deductive spot-check was not performed**, and the dispatch's
  "otherwise record in C4" branch was taken — but for a stronger reason than
  cost: it is not performable in this model. At finite propositional support
  every finite table list is the plausible-world set of some finite sentence
  set, so the live sets alone cannot separate Appendix D's generality from the
  deductive case. The separation lives in the sequence condition, which is what
  the alternating witness already exercises. Recorded as `FOLLOWUP_STOCK.md`
  item 5.
- **One continuation fixture was written, failed, and was replaced by a weaker
  true one.** It asserted that the two liability measures can differ when the
  opposition dies and the enforcer unwinds. They did not differ there, nor in a
  144-configuration scan. The fixture now asserts the agreement it found, and
  the open question — whether the enforcer's worth is monotone as a theorem or
  as an artifact of the fixture families — is `FOLLOWUP_STOCK.md` item 10.
- **C1's fixture family is two-coordinate**, which brushes the "full
  multi-coordinate cross-subsidy program" named out of scope. The dispatch
  requires the two-sentence recycling fixture explicitly, so the two-coordinate
  work here is the minimum C1 asks for and nothing beyond it: the general
  joint-margin question is stated and left in `FOLLOWUP_STOCK.md` items 1–3.

## What was not shown

No claim is registered or kernel-checked, and no Lean statement was attempted.
Six of C0's eight steps have no `Contrib` support; the promotion table names
each gap. C0 is proved in the model for the parent's attacker classes plus this
continuation's two recycling families, on one- and two-coordinate fixtures with
a stationary rational interval peg — not over arbitrary budgeted ecologies or
arbitrary rational polytopes, for which the model has exact projection only for
boxes and segments. (H4) is a hypothesis because C1 shows it cannot be dropped,
not because cross-coordinate behaviour is understood. C0′ rests on Theorem 4.4
and Theorem 3.4, both cited and not re-proved. C3's converse is twelve
configurations at one peg family, and its closed-form floor is a fit to those
twelve points, graded `bound-with-argument` for that reason. The Appendix D
subsection establishes the severance and the agreement condition's role by
witness and by exhaustive check on two schedules; it does not prove Theorem
D.1. The recycling threshold between compounding and self-defeating drain is
bracketed by two fixtures and not located.

## Outstanding maintainer actions

1. Rule on the continuation's provisional names — self-financing lemma,
   recycling coefficient, cross-coordinate subsidy, throttling world, billing
   world, gross capacity — queued in `DECISIONS.md`. One reading of `MEMO.md`
   continuation sections C1 and C0.
2. **Decide whether skeleton §6's affordability claim carries the
   no-cross-coordinate-subsidy hypothesis explicitly.** This is a correctness
   decision, not a presentational one: the continuation's channel-(c) witness
   shows a §6 stated without it would be false as stated. Queued in
   `DECISIONS.md` alongside item 1.
3. Decide whether the C0 theorem and the C0′ impossibility go into skeleton §6
   as written; both are marked paper-facing and are the adopted split's paper-1
   material.
4. Rule on whether the round's fixtures should move wholesale to the
   Definition 4.1 liability measure, or whether the monotonicity that makes the
   parent's measure equivalent is worth stating as a §6 lemma
   (`FOLLOWUP_STOCK.md` item 10).

## Recommended next pass

The follow-up paper's first item is `FOLLOWUP_STOCK.md` 1–3: what replaces
(H4). The evidence points at a *joint* margin over the constrained fragment
under which the enforcer's aggregate position is opposite the opposition's at a
common throttling world — the natural multi-coordinate generalization of the
discriminator this round isolated. Item 2's drain threshold is the cheapest
concrete entry point, since both endpoints are already fixtures.
