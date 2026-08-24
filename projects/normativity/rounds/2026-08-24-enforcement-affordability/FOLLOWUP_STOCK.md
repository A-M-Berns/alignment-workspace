# Follow-up stock

Material discovered while producing the paper-1 continuation (C0–C3) that
belongs to the **general affordability characterization** — the follow-up
paper — and is deliberately **undeveloped** here. Each entry carries a fixture
or file pointer so the follow-up can start from evidence rather than from
prose. Nothing below is a claim; several entries are open questions whose
answers this round did not attempt.

Status: research artifact, unregistered, `ci-only`.

## From C1 (the self-financing lemma)

1. **Multi-coordinate joint margin.** C0's (H4) forbids cross-coordinate
   subsidy outright because
   `TestC1SelfFinancing.test_self_referential_recycling_compounds_and_closes_nothing`
   shows a single unconstrained coordinate is enough to make a
   perfectly-margined coordinate's liability geometric. The general question is
   what replaces (H4): presumably a *joint* margin over the constrained
   fragment, under which the enforcer's aggregate position is opposite the
   opposition's aggregate position at some common throttling world. The
   fixture's two-coordinate geometry (`PEG` on `φ`, alternating bands on `ψ`)
   is the smallest instance; the pumped coordinate is the subsidy source and
   the static one is the victim.

2. **The recycling coefficient as a functional.** The schematic
   `L ≤ (chest + slack + κ·L)/m` wants `κ` defined as a property of the
   schedule pair, not of a run. In the fixture `κ` is effectively the fraction
   of the enforcer's per-cycle loss on `ψ` that lands at a `φ`-throttling
   world. Measured indirectly (chest ratio 1.257–1.270 per cycle at drain
   `1/8`); never defined. There is a threshold: at drain `1/8` the chest and
   the `φ` flow compound, at drain `1/4` both decay and the attack is
   self-defeating
   (`TestC1SelfFinancing.test_there_is_a_drain_threshold_above_which_the_attack_self_defeats`).
   Locating that threshold as a function of the two regions' geometry is the
   natural definition of `κ`, and was not pursued.

3. **Gross capacity versus realized drawdown.** The parameterized-chest form is
   unconditionally true with `W` = budget + income received at the throttling
   world, and false with `W` = realized drawdown there
   (`test_self_referential_recycling_compounds_and_closes_nothing` asserts the
   second fails: `W = 0.42` against liability `21.91`). Which parameterization
   the follow-up should carry — and whether gross capacity is bounded by
   anything schedule-local under a joint-margin hypothesis — is open.

4. **Sequential versus simultaneous subsidy.** The parent's G2 established that
   spreading flow across components does not relax the aggregate cap. The
   continuation's patsy fixture establishes the same for *sequential* transfer
   through an unconstrained sentence
   (`test_aggregate_nominal_chest_still_caps_patsy_recycling`). Whether the two
   compose — a subsidy chain of depth `k` — was not tested.

## From C2 (Appendix D)

5. **Non-deductive nested assessments are not exhibitable at finite support.**
   The C2 spot-check the dispatch allowed for could not be performed: at finite
   propositional support every finite table list is `PC(D)` for some finite
   sentence set, so the live sets alone cannot separate Appendix D's generality
   from the deductive case. The separation lives in the *sequence* condition —
   D.1's agreement hypothesis is weaker than nestedness of world sets — and the
   alternating-singletons witness exercises exactly that. Stating §6 at
   Appendix D's generality therefore needs a fixture family that varies the
   agreement condition rather than the deductiveness of each `L_n`; not built.

6. **Set-gap generalities.** The parent's set-gap path functional is stated for
   intervals in one coordinate. Its multi-coordinate form — whether
   `dist(K_n, K_{n+1})` in the product geometry is still the billable
   quantity when the regions are polytopes rather than boxes — was not touched.
   The round's model has exact projection only for `Box` and `Segment`
   (`src/market_model.py`), so a polytope projector is a prerequisite.

7. **Recharge composition.** The parent's vindication recharge (W4) and the
   continuation's cross-coordinate subsidy are two refill channels for the same
   war chest. Whether they compose multiplicatively, and whether a schedule can
   be affordable against each separately and unaffordable against both, is
   open; the two fixtures (`TestW4SettlementSurprise`,
   `TestC1SelfFinancing.test_self_referential_recycling_compounds_and_closes_nothing`)
   are built on compatible supports and could be merged directly.

## From C3

8. **The quantitative floor's true form.** `L ≥ m²/4(1−m)` is fitted to twelve
   configurations and is uniform in the flow size because larger flow trips the
   throttle sooner (`TestC3ConverseOfTheorem46`). The trade-off between flow
   size and sustained inventory has an optimum that the scan brackets but does
   not locate; the sharp floor is presumably attained at the flow that just
   avoids the exact-touch shutoff.

9. **The converse beyond a stationary interval peg.** C3 is checked at
   `K = [2/5, hi]` with `φ` undecided. Whether the biconditional survives
   region motion — where the parent's W3 shows liability can be positive for
   reasons unrelated to any excluded pattern — was not tested, and is the
   obvious way the remark could fail to generalize.

## Measurement

10. **Definition 4.1 versus the final-horizon deficit.** The round's
    `lifetime_liability` reads the enforcer's deficit at the final horizon;
    Definition 4.1 takes the supremum over horizons. The two coincide on every
    fixture in this round and across a scan over region, flow, side and budget
    (`TestParentSpotChecks.test_the_two_measures_agree_across_a_scan`), because
    the enforcer's cumulative worth is monotone along every run this model
    produces. **No separating instance is known.** Whether monotonicity is a
    theorem about the projection trade or an artifact of the fixture families
    is open; if it is a theorem it belongs in §6, and if it is not, every
    fixture in the round should move to the Definition 4.1 measure.
