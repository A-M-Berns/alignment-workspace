# Prosecution

## 1. The twenty attacks

Verdicts, and for each failure which of four things it is: **arc false** — the
claimed implication does not hold; **assumption** — the repair needs a
substantive but intelligible restriction; **already excluded** — the fixture
violates principal mediation before the repair is reached; **artifact** — a
consequence of how this model is built and not of the claim.

| # | attack | verdict | check |
|---|---|---|---|
| 1 | perfect prediction, same physical outcome, different mediation | separated by the response map; deficit `0` | `test_01_perfect_prediction_and_20_same_outcome_different_response` |
| 2 | imperfect prediction | bound is `2 B eps_pred = 1/2`, attained | `test_02_imperfect_prediction` |
| 3 | irreversible preparation before the choice is known | survives; the repair keeps the preparation | `test_03_04_05_06_early_commitment_in_its_four_forms` |
| 4 | feasible set depends on early commitment | same structure as 3 | same |
| 5 | noncommuting prepare and let-the-principal-choose | same structure as 3 | same |
| 6 | time-sensitive opportunity | same structure as 3; the hedge is the wait and costs half | same |
| 7 | information obtainable only by preemption | **not expressible** at one decision index | `test_07_information_obtainable_only_by_preemption` |
| 8 | resources whose acquisition changes the principal's decision process | capture; the composition catches it | `test_08_and_14_prediction_bought_by_capture` |
| 9 | the advisor's survival requires an early principal-level action | **assumption**; the same term as 12 | `test_09_survival_and_12_collapsed_range_are_the_same_term` |
| 10 | the advisor reproduces every principal effect | true for single choices, false for the map unless the principal is predictable | `test_10_the_advisor_reproduces_every_principal_effect` |
| 11 | bypass while the choice is nominally intact | **already excluded**; efficacy fires, `forecloses` is silent | `test_11_bypass_while_nominally_intact` |
| 12 | one advisor policy collapses the principal's range | **assumption**; `foreclosure_premium = 1/2`, invisible to the bound | `test_09_survival_and_12_collapsed_range_are_the_same_term` |
| 13 | the principal chooses what the advisor rejects after full update | **arc false** off the acceleration class; `eps_pred = 0`, deficit `2B` | `test_13_the_principal_chooses_what_the_advisor_rejects` |
| 14 | the advisor predicts perfectly because it controls the principal | **already excluded**; the intervention is not a map | `test_08_and_14_prediction_bought_by_capture` |
| 15 | spoofed authorization metadata | **unbuildable**; there is no field | `test_15_spoofed_provenance_has_nothing_to_write` |
| 16 | legitimate persuasion changes the choice | permitted; no clause fires | `test_16_legitimate_persuasion_stays_permitted` |
| 17 | transient capture and restoration | caught along the run; endpoints agree | `test_17_transient_capture` |
| 18 | universal deprivation of due reasons | **this round's clauses are silent**; coverage fires | `test_18_universal_deprivation` |
| 19 | manipulation preceding an apparently valid transfer | endpoint rule certifies both arms; process refuses; the ledger refuses the self-release form | `test_19_manipulation_before_an_apparently_valid_transfer` |
| 20 | same terminal outcome, different counterfactual response maps | same as 1 | `test_01_...` |

Attacks 3 to 6 are one structure and the round says so rather than building four
near-duplicate fixtures for it: an action taken before the choice is known whose
value depends on the choice.

## 2. The condition that is doing the work, and what it is not

The dispatch asks whether *all ordinary benefits of early commitment admit
contingent preparation* is secretly carrying the result. It is not, and the
reason is the shape of the repair.

`Repair` does not re-plan. It keeps the preparation and changes only the channel,
so it never has to find a contingent substitute for a committed action. Attacks 3
to 6 are attacks on a repair that would have to; against this one they cost
nothing beyond `eps_pred`.

What is carrying the result is weaker and is visible in the code:

> **Late binding.** For every preemptive conduct, the conduct with the same
> preparation, the same implementation table and the identity channel is
> admissible.

Late binding fails exactly when the preparation writes the choice — when
`residual` is a singleton — and then the repair is not merely lossy but
uninformative, because the repaired conduct is mediated over a choice set with
one element. That is `foreclosure_premium`, it is `PRINCIPAL_MEDIATION.md` §2's
efficacy clause, and it is an assumption about the **preparation set**, not about
what the conduct prefers.

So the bottleneck is intelligible and it is not preemption-aversion: it is a
claim about which physical preparations are available, false in nameable
environments, and checkable from the dynamics.

## 3. Where the model's own commitment is exposed

`model.response` reads a surgical intervention: it sets the principal's choice
and does not propagate to what `A` used to predict it. Where `A` authors the
choice those are one coordinate and there is no such intervention.

The condition is checked, not assumed: the selector must take one value inside
each licensed-reason group. It fails on the legitimacy round's own
`manufactured_trust`, where the advisor replaces the adequacy relation and the
selector moves with it, and holds on the persuasion control, where the arms that
differ are in different groups. Grouping is what keeps the condition from
refusing persuasion.

The residue is Proposition 8's fence, unmoved: no criterion computable from one
realized instance separates the two conducts. The round states its criterion on
the conduct and does not claim otherwise.

## 4. The price the efficacy clause pays

Cellwise efficacy entails the selector is not constant on a cell of `A`'s
information, so it is false of a perfectly predictable principal, which the
programme is forbidden to rule out. With Proposition 1 that gives:

> No condition on realized data is both non-vacuous and compatible with a
> perfectly predictable principal.

This is a cost of the interface and not a defect of the fixture. A reader who
wants a mediation condition that survives a perfectly predictable principal has
to accept that it will not be a condition on runs.

## 5. Controls: could the model have said anything else?

- **Preemption strictly beats every mediated conduct somewhere.** Without this
  the repair lemma would be about an empty problem.
- **The bound is not vacuous**: some conducts have strictly positive deficit, and
  one attains `2B`.
- **The repair is not to the class optimum.** On the overriding member of the
  fully updated class it lands at `-1/2`, below the mediated optimum.
- **`mediated` is a one-in-four condition** on the two-choice alphabet, so it is
  not a formality most conducts satisfy.
- **The predictor is optimal**: `eps_pred` is the minimum over every
  cell-measurable predictor, on every preparation of every episode.
- **Each clause of the interface accepts a delegate**, so the interface is not so
  strong that nothing passes.
- **Every clause fails alone somewhere**, so the conjunction is not one clause
  under three names.
- **No float appears in any source file**, checked by reading the sources rather
  than by sampling values.

## 6. What is not prosecuted

Coordinated advisors. Anything asymptotic. Any cross-index structure, which is
where foreclosure of a later correction lives. A general form of the preparation
type: `residual` is one way a preparation can constrain the principal and the
round has no argument that it is the general one.
