# Part A — rebuttal by settlement: the rule, and what it changes

Lean: `Workspace.Normativity.Contrib.WarrantEntitlement`, sections *Part A (round 2026-10-21)*
and the `Fixture`/`Fixture2` namespaces (`lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean`).
Exact rationals: `src/rebuttal.py`, `src/exhibit.py`, run by `tests/run.py`.

## A1. The rule

The rulings M1–M3 as a function on the form, not on the specialized row — the form knows
which coordinate is antecedent and which consequent, the row does not (P1):

```
inductive Outcome | kept | rebutted | vacuous | retired

settleOutcome F (premise X c)              = if F pins X false then retired else kept
settleOutcome F (applicability X XA c)     = if F pins X false then vacuous
                                             else if F pins XA false then rebutted else kept
settleOutcome F (strength XA XAY c)        = if F pins XA false then vacuous
                                             else if F pins XAY false then rebutted else kept

settleForm F o = if settleOutcome F o.form = kept then some [specialize F o.form.row] else none
```

Vacuity is checked before rebuttal: a form that never applied is not rebutted (an
agent-decided detail; the row leaves either way). Everything is `Decidable`.

**Soundness, in P1's form.** `settleForm_eq_some_iff`: `settleForm F o = some rows ↔ rows =
[specialize F o.form.row] ∧ ¬ Degenerate F o.form`, where `Degenerate` is the disjunction of
the three pinned-false conditions; `settleForm_eq_none_iff` is the complement. **What the
removed rows say**: `strength_contraposes` — a strength row whose consequent is pinned false
forces its antecedent to `0` at every pinned point (`c > 0`); `applicability_contraposes`
likewise. `settleOutcome_rebutted_iff`: a strength form is rebutted exactly when its
consequent is pinned false and its antecedent is not. **M3**: `settleForm_strength` — the kept
row is the specialization of the form with its own strength; nothing is discounted.

**Grounds under settlement.** `retiredIds G F` (the retired premises), `citesRetired` (an
occurrence whose `cites` names a retired occurrence), and

```
Grounds.survivors G st F = G.filter (o ↦ o.id ∉ st.defeated ∧ settleOutcome F o.form = kept
                                          ∧ ¬ citesRetired G F o)
Grounds.settledBundle G st F = survivors' specialized rows, cited by occurrence, ++ the pins
Grounds.settledRegion G st F = Bundle.Region (settledBundle)
```

`Grounds.settledRegion_iff`: the settled region is the cube, the pins, and the survivors'
rows (`regionOn`). `region_subset_settledRegion`: the port-only region of the warrant round
sits inside it — settling forms only removes rows.

**Retirement reaches the warrant one step along `cites`**, and otherwise through the
settlement's closure: a conditional form whose antecedent is the retired premise is vacuous
on its own; a form further down a chain leaves when the closure pins its antecedent false.
The fixtures' settlements carry their closure (`X` false pins `X∧A`, `X∧A∧Y` false). Without
closure a chain of length three keeps its last link
(`tests/test_rebuttal.py::test_retirement_needs_closure`); the transitive rule is item 121.

## A2. The orphan cannot form (`Fixture`)

The warrant round's fixture, `X, X∧A, X∧A∧Y, Y`, `c_P, c_A, c_S ∈ (0,1)`, applicability port
`2` defeated at `n₀`, `Y` refuted at `n_E` with its closure (`settlementAt`, `docketAt`).

- `survivors_eq`: at every date the survivors are the premise, the applicability before `n₀`,
  the strength before `n_E` — by `settleForm` (`settleOutcome_strength` is `rebutted` exactly
  from `n_E`), not by declaration. `schedRebutted_eq_survivors`: the force schedule the
  enforcer holds is the survivors through the bridge `toForceRow`.
- `no_strength_after`: from `n_E` the strength row is not among the enforced rows, and once
  the port is defeated the only row is the premise. **The harmonic buyer of the warrant round
  has nothing to buy against**: the enforcer holds no row in `X∧A`
  (`src/exhibit.py::nothing_to_buy`, `test_no_row_on_XA_after_rebuttal`).
- `rebutted_region_nonempty`: the region after the rebuttal contains `(1, c_A, 0, 0)`; the
  world `X, A` true, `Y` false (`wAY`) is live and clears every live row
  (`gap_dominated_wAY`).
- `liability_rebutted`: at every live world at every date the enforcer's assessed net worth
  is at least **`−3ρ(2 + ρ)`**, `ρ = max_j c_j/(1 − c_j)`.

**The dispatch said "the same `3ρ`"; the construction gives `3ρ(2 + ρ)`, and the smaller
bound is false.** Before `n_E` the bound is `3ρ` with the all-true world as the slack
witness (the warrant round's theorem). Across the rebuttal the slack witness changes — the
all-true world dies with `Y` — and the bankroll is the two-witness theorem
`netWorth_ge_neg_odds_reopened`: pre-reopening net worth `≥ −3ρ`; post-reopening slack mass
at the new witness `< 3 +` (the reopened mass, itself `≤ 3ρ`); total `≥ −3ρ − ρ(3 + 3ρ)`. The
reopened mass is real: a counterparty that sold `X∧A∧Y` against the strength row while the
all-true world was live is, after the rebuttal, ahead by `c_S U_S` at every live world (the
sentence is false), and the trading firm's floor is on *cumulative* worth at live worlds, so
it can now sell `X∧A` against the applicability row with that cushion.
`src/exhibit.py::cushion_exhibit` runs the two phases on the fixture: `U_S = 9`,
reopened mass `6`, `U_A = 32`, the enforcer's loss at the world `X` true, `A` false is
**`24 > 12 = 3ρ`**, within the sharp per-row accounting `odds_A(3 + 3·odds_S) = 27` and the
proved uniform bound `72`, and consistent with the maker's constant (the enforcer is at `+2`
at the other live world). `test-supported`; the Lean proves the upper bound only.

## A3. The premise guard retired (`Fixture2`)

Five coordinates `X, X∧A, X∧A∧Y, Y, Z`; the first warrant's three occurrences and a second
warrant `P(Z) ≥ c_Z` on the disjoint sentence; the settlement `refuteX` pins `X` false with its
closure.

- `old_rule_empty`: under the port-only region the premise row `P(X) ≥ c_P > 0` meets the pin
  `P(X) = 0` and the joint region is empty — force on `Z` is withheld with it. **This is the
  countermodel to the warrant round's reading "the premise row guards the chain"**: the guard
  also guarded the unrelated warrant out of existence.
- `survivors_refuteX`: under the rule the survivors are `[occZ]` — the premise retired, the
  applicability and strength vacuous.
- `retired_region`: the settled region is nonempty (`(0, 0, 0, 0, c_Z)`) and every point has
  `c_Z ≤ x_Z`: the second warrant is enforced exactly as before.

## A4. Monotonicity restated

**What was true and stays true.** `IsForcedInterval.mono` and `forcedInterval_mono` are
statements about `forcedRegion` — the region of the *unspecialized* rows under growing
settlement, with the row set fixed — and they remain true as stated; both are landed in
`SeedStatics.lean` unchanged. The prompt's "false under M1–M2 in their current form" is a
correction: what fails is their transfer to the **settled** region, where the row set depends
on the settlement.

**The failure.** `Countermodel.settled_not_anti`: one applicability form `P(1) ≥ P(0)/2` on
two coordinates; the empty settlement and the settlement pinning the consequent false. The
point `(1, 0)` is in the settled region after the pin (the row was rebutted) and not before:
more settlement, larger region.

**(a) No reopening, nested as before.** `survivors_anti`: under more settlement survivors only
leave (`kept_of_le`, `retired_of_le`, `retiredIds_mono`). `settledRegion_anti_of_survivors_eq`:
when the survivors are unchanged by the step, the settled region shrinks — intervals nest.

**(b) The exact widening bound.** `settledRegion_subset_kept`: for `F ≤ F'`, the settled
region after the step and the settled region before it both lie inside `regionOn (survivors
F') F` — the region the *kept* rows forced at the pre-step settlement. `reopening_bound`: any
bounds valid on that region are valid on both settled regions. So the interval on a
coordinate can widen by at most the width the removed rows had been forcing off the kept
rows' interval; on the fixture the removed strength row had forced nothing on `X∧A` at the
pre-step settlement (`X∧A∧Y` free in `[0,1]` makes `P(X∧A∧Y) ≥ c_S P(X∧A)` inactive upward),
the allowed widening is `0`, and the actual widening is `0` — the bound is attained with
equality (`EndToEndWitness.Run.rebuttal_step`, `test_reopening_widens_XA_by_zero`). What the
rule prevents on the fixture is a *contraction*: the port-only region pins `X∧A` to `0` there
(`Run.old_rule_pins`).

**Registry.** Neither `IsForcedInterval.mono` nor `forcedInterval_mono` was registered as of
PR #129 (confirmed: the registry's seed-related entries are this round's); nothing is
superseded in the registry.

## A5. Re-verification of the warrant round's theorems

| theorem | status under `settleForm` |
|---|---|
| `netWorth_ge_neg_odds`, `liability_of_odds`, `warrant_normative_inductor` | **unchanged** — about the rows a schedule holds, not where they came from; reused verbatim by `liability_rebutted` and the witness |
| `netWorth_ge_neg_odds_reopened` | **new** — the two-witness form the rule needs across a reopening |
| `Fixture.liability`, `Fixture.liability_disagree` | unchanged as statements about their schedules (`schedLive`, `schedWithheld`); `schedWithheld` is now a *superseded reading* — under the rule force is not withheld at `n_E`, the strength row leaves and `schedRebutted` is the schedule |
| `Fixture.disagree_region_empty` | **true of the port-only region only**; under the rule the region is nonempty (`rebutted_region_nonempty`). Kept, its docstring now says which region it is about |
| `Fixture.orphan_region_nonempty`, `orphan_no_slack` | **kept as the countermodel to the port-only rule**; under `settleForm` the orphan cannot form (`no_strength_after`) |
| `Countermodel.*` (Part A of the warrant round), `licence_chain` and the record lemmas | unchanged — the licence chain is on `Grounds.bundle`; its settled-bundle form is item 115's business |
| `IsForcedInterval.mono`, `forcedInterval_mono` (ported) | unchanged and true; not transferable to the settled region (A4) |

## Items

113 is answered by the rule (narrowed to its remainder); 112's orphan cannot form under the
rule (narrowed to transitive propagation, item 121); 114 stays open and gains the cushion
exhibit as a second instance (item 123).
