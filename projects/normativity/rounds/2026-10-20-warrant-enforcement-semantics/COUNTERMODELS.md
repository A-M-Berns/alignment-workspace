# Countermodels and obstructions, each with its fixture

| § | claim refuted or obstruction | fixture | where |
|---|---|---|---|
| 1 | `Admissible → Supported` | two duplicating occurrences, one defeated | `Countermodel.admissible_not_supported`; `src/licence.py` |
| 2 | `Supported → Licensed` | two verdicts in `[1/2, 1]`, one unauthorized selection | `Countermodel.supported_not_licensed`, `selection_not_transparent` |
| 3 | a bankroll exists for every nonempty region | the orphaned strength row after defeat and refutation | `Fixture.orphan_region_nonempty`, `orphan_no_slack`; `src/fixture.py::harmonic_buyer_run` |
| 4 | B(ii): liability unbounded when the evaluation is unconstrained | the disagreeing evaluation with the chain live | `Fixture.liability_disagree`, `disagree_region_empty` |
| 5 | item 39 strong | two worlds, one payout vector | `same_projection_different_support` |
| 6 | the record is injective / constant in the run | two clearing prices; one defeat | `RecordFixture.trace_not_injective`, `trace_not_const` |
| 7 | a licence may cite rows by value (`Bundle.Allowed`) | §1 again | `Grounds.mem_bundle_iff` against `Allowed` |

## 1. Admissible, not supported

One coordinate; `r₁`, `r₂` both `P(φ) ≥ 1/2`; the region `[1/2, 1]` before and after defeating
port `1` (`region_unchanged`). The certificate citing `r₁` has its lower row admitted on the
quiet docket (`cited_quiet`) and refused on `stDefeat` (`stale_not_supported`: the bundle is
`[⟨Cite.sub 2, row⟩]`, the citation `Cite.sub 1` is absent, and the row is neither cube face
since its constant is `−1/2`). A certificate citing `r₂` passes (`fresh_supported`). Exact
rationals in `src/licence.py`: `forced_interval(G, set()) = forced_interval(G, {1}) = (1/2, 1)`,
`supported(G, {1}, 1/2, Certificate(lower_cite=1)) = False`,
`supported(G, {1}, 1/2, Certificate(lower_cite=2)) = True`.

## 2. Supported, not licensed

Same region, verdicts `2/3` and `3/4`, both supported by `cert 1`. `recordAuth` authorizes
event `7` and `recordNoAuth` does not; the licence differs on nothing else. The selection is
a transparency failure: with the advisor's contribution at event `0` being the selected
verdict, two continuations with the same declared inputs and different contributions fail
`TransparentAt` for every reference `κ` (`selection_not_transparent`, an application of
`GateIsLegitimacy.tiebreak_transparency`).

## 3. The orphan pin — the one unaffordable case *(under the port-only rule)*

> **Superseded 2026-10-21.** Under rebuttal by settlement the strength row leaves at the
> refutation and this obstruction cannot form (`Fixture.no_strength_after`); it is kept as the
> countermodel to the port-only rule. The closing sentence of this section, "the premise row
> guards the chain", is retracted: see `../2026-10-21-rebuttal-and-end-to-end/REBUTTAL.md` A3.

State: `X` settled true, applicability port `2` defeated, `Y` refuted (`settledDisagree`
pins `X = 1`, `X∧A∧Y = 0`, `Y = 0`). Live rows: premise `P(X) ≥ c_P` and strength
`P(X∧A∧Y) ≥ c_S P(X∧A)`. The region contains `(1, 0, 0, 0)` (`orphan_region_nonempty`), so
the compiler does not withhold force. The strength row reads `c_S · P(X∧A) ≤ 0`: the enforcer
shorts `X∧A` at any positive price. Live worlds: `(1, 0, 0)` with gap `0` and `(1, 1, 0)` with
gap `−c_S`; no live world has positive gap (`orphan_no_slack`). The bankroll hypothesis fails
and no `B` exists:

`harmonic_buyer_run(β = 10, c_S = 2/3, n)` buys `k_t = 1/(t+1)` units of `X∧A` a day; the
maker zeroes the aggregate at `p_t = k_t/(c_S² β) = 9k_t/40`.

| dates `n` | enforcer at `(1,1,0)` | buyer's spend at `(1,0,0)` | `H_n` |
|---|---|---|---|
| 10 | `−2.58…` | `0.3487…` | `2.9290…` |
| 50 | `−4.13…` | `0.3657…` | `4.4992…` |
| 200 | `−5.51…` | `0.3690…` | `5.8780…` |

Exact rationals in the test; the loss is `≤ −(H_n − spend)` and `H_n ≥ ln n`, so it passes
every bound; the spend is `≤ (9/40) Σ 1/(t+1)² < 0.37`, inside any budget `≥ 1`. The
buyer's schedule is fixed and rational, hence efficiently computable; it reads no price.

With the applicability row **live**, the same refutation empties the region
(`disagree_region_empty`) and force is withheld: the premise row guards the chain, and the
per-row defeat removed the guard. Items 112 and 113.

## 4. B(ii)'s expected unboundedness

`Fixture.liability_disagree`: with the evaluation `¬Y` at `n_E` and the applicability row
live, `−3ρ` at every live world at every date. The deficit is realized and paid within the
bound; the region empties at `n_E` and the account freezes. The expectation is refuted on
the fixture; the mechanism that would make it true (an evaluation foreknown while the
agreeing world is still assessed live) is not among the round's objects.

## 5. Item 39, the pair

`(X, A, Y) = (0, 0, 0)` and `(0, 1, 0)` have payout `(0, 0, 0, 0)` on `(X, X∧A, X∧A∧Y, Y)`.
Two point masses, one projection, two live worlds. The operative weakness is that the
premise row excludes every `X`-false live world as a point (`test_the_region_excludes_live_points`).

## 6. The record

`baseRun (1/2)` and `baseRun 1` differ and have one record; `defeatRun` has another. In
`src/record.py`: `trace(MarketRun(1/2)) == trace(MarketRun(1))`,
`trace(MarketRun(1/2)) != trace(MarketRun(1/2, defeated={1}))`, and
`trace(MarketRun(0)).position == 1`.

## 7. Citing by value

`Bundle.Allowed` admits a row when *some* cited row of the bundle has that value. Under it
§1's stale certificate would pass after the defeat, because `r₂`'s row has the same value.
`VerdictCert.RowAdmitted` admits `⟨q, r⟩` only under the citation `q`; `Grounds.mem_bundle_iff`
says exactly which `⟨q, r⟩` are present. This is the content of item 56's citation
discipline and the reason `Supported` is not a typing discipline.
