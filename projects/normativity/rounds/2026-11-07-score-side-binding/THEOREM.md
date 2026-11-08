# Where obligations bind — statements of record and assumption ledgers

Every named object is a declaration under `lean/Workspace/Normativity/Contrib/`. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace` from `lean/`, then
`python3 tests/audit_axioms.py`. Each module ends with its `#print axioms` list; every result
audits to `[propext, Classical.choice, Quot.sound]`.

## 1. The score-side test (`WarrantInductorScoreSide`)

**Setting.** The rebuttal run's schedule `WB`, deductive process `DP`, states `NB n`, decision
problem `P₁` (act on `X∧A∧Y` or refrain; `τ = 1/3`, `δ = 1/12`, preference `1`). The obligation
on conduct **refrain while live**: acting is a shortfall at any date at which the originating
obligation's account (occurrence `0` of `state₀`) carries a live leaf, assessed by that
account's fate (`ShortfallAt`; `shortfall_assessed`: live at every date). Its shortfall
sentence `σ` is the application's; its price at date `n` is `WB.market DP n σ`. The
**score-side realization** `scoreSide σ ϖ` is the triple (the run's schedule, the obligation,
the charge `ϖ`); its gate is the soft gate on `chargedScore = P₁.scoreR − ϖ · pS`, with
`pS = (price of σ, 0)`.

**Theorem** (`same_question_two_realizations`, registered
`scoreside.same-question-two-realizations`). For every `σ`, every `ϖ ≥ 0` with
`ϖ · WB.market DP 4 σ ≤ 19/240`:

1. the run's own gate acts with mass `≥ 24/25` at date `4` and refrains with certainty at
   date `9` (`WarrantInductorRebuttal.same_question`);
2. the score-side gate acts with mass `≥ 24/25` at date `4` (`before`) and refrains with
   certainty at date `9` (`after`, for every `ϖ ≥ 0`).

Beside it: `bundle_unchanged` (the score-side enforcer's bundle is `(NB n).bundle` at every
date), `market_unchanged` (`rfl`: the market is `WB.market DP`), `no_conduct_row` (no held
row equals `conductRow = ⟨e_{XAY}, 1/3⟩`, by the constants of the held rows:
`bundle_row_b_ne`), `scoreGate_zero` (at `ϖ = 0` the two gates coincide), `override` (if
`ϖ · price ≥ scoreR(act) − τ` the act's weight is `0`).

**Theorem** (`conduct_on_prices_conflicts`, registered
`scoreside.conduct-on-prices-conflicts`). `¬ ∃ x, ((NB 4).bundle ++ [conductRow]).Region x`,
by the certificate `conductCert = (1 · rowS4, 2/3 · rowA4, 1 · conductRow)` with constant
`−1/6`, through `conflict_sound`. And `conduct_on_prices_idle`: every point of `(NB 9).region`
satisfies `conductRow`.

**Hypotheses.** `before`: `0 ≤ ϖ` and the charge bound `19/240`, which is
`(1/2 − 1/240) − 5/12`, the room the enforced strength and applicability rows
(`excess ≤ 1/400`) leave above `τ + δ`. `after`: `0 ≤ ϖ`. Everything else is the run's
(`inductor`'s conformance at enforced dates, `memS4`, `memA4`, `memA9`, `memPin9`). Nothing is
assumed about `σ` beyond its being a sentence; its price is read from the run's market.

**What inhabits it.** Any sentence and `ϖ = 0` (then `hsmall` is `0 ≤ 19/240`); the gate at
`ϖ = 0` is the run's.

**What is typed.** The shortfall sentence `σ` and its generability; the assessment's relation
to the market's price of `σ` (nothing says the market prices the assessment well).

**What would make it vacuous.** A market at which `WB.market DP 4 σ` is so large that
`hsmall` fails for every `ϖ > 0` — then only `ϖ = 0` satisfies it, and the theorem reduces to
the run's. `override` covers that regime.

## 2. Solvency as soundness, and the conflict audit (`WarrantSolvency`)

**Setting.** A `Schema`: strength `c : ℚ`, `undefeated : ℕ → Bool`, `consequent : ℕ → Bool`.
`held t = c` on an undefeated instance, `0` otherwise; `realized t` the consequent's truth
(`1`/`0`) on an undefeated instance, `0` otherwise. `UnitPosition v`: `v t = realized t − held t`
for every `t`.

**Theorem** (`Schema.bounded_iff_frequency`, registered `solvency.bounded-iff-frequency`).
`(∀ n, −B ≤ liability realized held n) ↔ ∀ n, c · U_n − T_n ≤ B`, with `U_n` the undefeated
count and `T_n` the true count among them (`outperformance_eq`). `solvent_iff`: the same for
any `v` under `UnitPosition`.

**Hypotheses.** None beyond the schema; the unit-position reduction is the named hypothesis of
`solvent_iff`. **Inhabitants.** `Witness.alwaysTrue` (bounded at `B = 0`), `Witness.alwaysFalse`
(unbounded, by `systematic_outperformance_unbounded` with gap `3/4`). **Typed.** The relation
between `WarrantForce`'s calibrated day value and a unit position per instance; timeliness is
the shape of the data (`consequent : ℕ → Bool`). **The same theorem elsewhere.**
`DecisionComponent.bounded_iff_not_outperformed` with `h := realized`, `g := held`; this is
that theorem renamed, not new mathematics.

**Theorem** (`suspect_in_bundle`, registered `solvency.conflict-names-suspects`). For a bundle
`B`, a `FarkasCert` whose rows are `B.Allowed`, and `x ∈ InCube`: some `i` with `0 < mult i`
has `row i` a row of `B` and `¬ (row i).Sat x`. From `exists_violated_suspect` (every
certificate, every `x`, no cube hypothesis). Corollaries: `no_conflict_of_sound`,
`unique_suspect`, `suspect_in_normState`.

**Hypotheses.** The certificate's rows are allowed rows of the bundle (the compile's `Valid`
condition for a `conflict` result); `x` in the cube. **Typed.** Which point is "the true
posterior"; the theorem holds at every cube point.

## 3. The robust reading on the eight-world model (`RobustWarrant`)

**Setting.** Worlds `Bool × Bool × Bool` (quantity, signal, challenge); `μ` the product
measure (uniform prior, signal accuracy `3/4`, challenge accuracy `2/3`). `Aev` the signal
true, `Yev` the quantity true, `Cev` the challenge contrary, `Ccev` concurring.
`Robust μ A Y c U := ∀ E ∈ U, 0 < μ(A∩E) → c · μ(A∩E) ≤ μ(A∩Y∩E)`;
`robustStrength` the least `μ(A∩Y∩E)/μ(A∩E)` over `E ∈ U` with `A∩E` possible.

**Theorem** (`robustStrength_all`, registered `robust.eight-world-strengths`).
`robustStrength μ Aev Yev {univ, Cev, Ccev} = 3/5`. Beside it: `robustStrength_defeated = 3/4`
over `{univ, Ccev}`; `robust_all_iff`, `robust_defeated_iff`, `against_robust_iff` (the
opposing warrant's strength is `2/5`); `robust_meet` (`3/5 ≤ y ∧ 2/5 ≤ 1 − y ↔ y = 3/5`);
`robust_sound` (a robust warrant's row is valid at every undefeated record of positive mass);
`valid_at_signal`, `invalid_at_contrary`; `kept_under_challenge`, `not_undercut`,
`contributed_row_invalid` on the three-coordinate embedding; `naiveCert`, `naive_conflict`.

**Hypotheses.** None beyond the stated model. **Inhabitants.** The model itself; `mass_univ`.
**Typed.** Which extensions are undefeated — `U` is an input; the fixture declares two sets.
**What would make it vacuous.** An empty `U`, excluded by `Uall_nonempty`. **The same
theorem elsewhere.** None; the eight-world model is not exposed in Lean elsewhere
(`ThinLegitimacy` §11 mentions one in prose). **Not shown.** Any `Form`-level rule or compile
of the robust reading (item 133).

## 4. Admission by standing (`AdmissionByStanding`)

**Setting.** `admittedByStanding allocAt matter issuer h o r := ((allocAt h).entry (matter o)).holder = issuer o`;
`withStanding S …` replaces a protocol's `Admitted`. The fixture: `issuer = (principal, agent)`,
`J₀` with each obligation its own matter held by its issuer, `protocolS`, `stateS = initialS.state`
over `start`; `J₁ = J₀.withHolder 0 agent`, `protocolS₁`.

**Theorem** (`reallocated_entitles_nothing`, registered `standing.reallocated-entitles-nothing`).
For every `O : ObligationState protocolS₁ wAnchor`, every `Expresses`, every
`E : Entitlement O grounds Expresses` and `o ∈ grounds`: `E.origin o ≠ 0`. Beside it:
`entitlementS n : Entitlement stateS (N n).grounds (fun _ _ => True)` (inhabited at every
date), `admitted_by_allocation`, `first_person_admitted`, `reallocated_not_admitted`,
`not_admitted_of_withHolder` (general).

**Hypotheses.** The entitlement's own fields; the allocation is constant in the history at the
fixture (`fun _ => J₀`), a history-dependent allocation being the general case the definition
takes. **Typed.** `Expresses` (total at the fixture); exposure is content-free at the fixture
(`start.exposed = univ`). **The same theorem elsewhere.**
`WarrantInductorWitness.answered_not_entitled`, with the account's fate replaced by the
allocation's holder. **Not shown.** Anything about `authorized` against the account (item
128(b)); entitlement along an evolution (128(c)).
