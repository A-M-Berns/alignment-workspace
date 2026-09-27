# The corrigibility kernel, phase 2: the headline, the rulings, registration (2026-09-27)

THE-HEADLINE-IS-BUILT-ON-THE-RULINGS-CORRIGIBILITY-A-PROPERTY-OF-PREFERENCES-WITH-FAITHFULNESS-AND-REALIZED-CORRIGIBILITY-KEPT-APART-LEGITIMACY-ONE-TIME-INDEXED-PREDICATE-PROVED-EQUIVALENT-TO-THE-LANDED-GATE-AND-SPLIT-THE-FIDELITY-SCORE-AVERAGED-OVER-DECISIONS-WITH-COUNTS-SUMMED-AND-THE-SUMMED-FORM-REFUTED-BOX-2-RESTATED-AT-THE-MARGIN-VARPI-MINUS-D-MINUS-W-LO-THE-SUBJECTIVE-EXCHANGE-RATE-PROVED-THE-LEARNING-MATERIAL-AN-EXTENSION-BEHIND-A-DECISION-INTERFACE-WITH-BRIA-AND-EXPLORATION-AS-ITS-REALIZATIONS-THE-HOUSE-SALE-WITNESS-INHABITING-THE-PACKAGE-AND-THIRTEEN-CLAIMS-REGISTERED — corrigibility is the agent's preference for every course it knows to be faithful over every course it knows to be unfaithful at a fixed exchange rate for risk, faithfulness the property of histories it is about and realized corrigibility what the theorems deliver; legitimacy is `L_t(h)`, "as of `t` her judgment is legitimately hers", defined by the landed conditions on the record up to `t` and proved to be the landed gate over the span, with the after-compromise round's two predicates its values at two times on the consultation model and every row's verdict kept, the void rule and the content residual stated with it; the fidelity score of a history is the mean of the per-decision evaluations less `ϖ` times the summed count, the hierarchy holds per decision and per history, and with summed evaluations it fails; Box 2's dominance margin is `ϖ − (D − w_lo)` because the mediated branch may itself be compromised, the landed `ϖ − D` its legitimate case; the headline's agent is a plain maximizer of the fidelity score whose own priced probability of unfaithfulness on any option it prefers to asking is at most `(D − c)/ϖ`; the learning material is an extension whose decision interface yields the realized violation rate `avg (D − c_k)/ϖ + ε̄ θ_hi + (B(K) + M(K))/(ϖ Σ w_k)`, met by Continuation BRIA with no exploration and by a maximizer over the inductor with restricted exploration and unbiasedness from feedback supplying `B(K)`; the promoted definitions sit in the specification layer by re-declaration with the landed originals unchanged; the house-sale allocation runs through the boxes at `ϖ = 25` in Lean and in an exact fixture; the headline's statements are registered against a filed item, the rulings are landed as dated decisions, the phase-1 queue is closed, and the specification is plain language first with Lean names in its final table only.

Reading order: [`SPEC.md`](SPEC.md) (version 2: the three notions, the primitives with
`L_t` and its eight cases, faithfulness, the fidelity score with its aggregation, the
permission layer demoted, Boxes 1–3 and the subjective exchange rate for a maximizer, the
extension, the interface contracts, the realization table), [`NOTATION.md`](NOTATION.md)
(the post's letters to the Lean names), then [`REPORT.md`](REPORT.md) (each ruling as
carried out, the deviations, what is not shown, the read-through check).  Lean:
`lean/Workspace/Deference/Spec/Headline.lean` (the specification layer: the promoted
definitions, `L_t` with its equivalences, the aggregation theorems, the boxes, the
subjective exchange rate, the house-sale witness) and
`lean/Workspace/Deference/Contrib/KernelExtension.lean` (the decision interface, the
realized-rate theorem, the two realizations).  Fixtures: `src/house_sale.py`, run by
`python3 tests/run.py`.  Wiki: `Corrigibility.md` rewritten, `Legitimacy.md`,
`Continuation-BRIA.md`, `Theorem-Spine.md`, `Glossary.md`.  Registry:
`projects/deference/CLAIMS.md`, the `kernel.*` entries against item 104.  Consumes
`../2026-09-26-corrigibility-kernel/` and the rounds it consumed.

Amended the same day by the follow-up
(`prompts/2026-09-27-corrigibility-kernel-phase2/FOLLOWUP.md`; `REPORT.md`, final
section): corrigibility is the preference property, not "maximizes the fidelity score"
(`Headline.Corrigible`, the generic and the not-aligned witness); `L_t(h)` is one property
of the history at a canonical formation point computed from it (`Headline.Legitimate`);
the exploration set's third clause is dropped and kept as the variant "exploration above
asking", with the lock-in fixture `src/exploration_lockin.py`.
