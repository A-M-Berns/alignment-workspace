# Where obligations bind — statements of record and assumption ledgers

Every named object is a declaration under `lean/Workspace/Normativity/Contrib/`. Rerun:
`~/.claude/scripts/safe-lake.sh build Workspace` from `lean/`, then
`python3 tests/audit_axioms.py`. Each module ends with its `#print axioms` list; every result
audits to `[propext, Classical.choice, Quot.sound]`.

## 1. The score-side test (`WarrantInductorScoreSide`)

**Setting.** The rebuttal run's schedule `WB`, deductive process `DP`, states `NB n`, decision
problem `P₁` (act on `X∧A∧Y` or refrain; `τ = 1/3`, `δ = 1/12`, preference `1`). The obligation
on conduct **refrain while live**: acting is a shortfall at any date at which the originating
obligation's account (occurrence `0` of the state accounted at that date, `stateAt n`, which is
`state₀` at every date of the run) carries a live leaf (`ShortfallAt`; `shortfall_assessed`: live
at every date). The obligation `O : RefrainWhileLive` carries one shortfall sentence per date,
`O.shortfall n`, priced at `WB.market DP n (O.shortfall n)`. **`Assessed O v`**: the valuation
`v : PCWorld` makes `O.shortfall n` true iff `ShortfallAt n`, for every `n`. The **score-side
realization** `scoreSide O ϖ` stores the run's schedule with the obligation and the charge `ϖ`;
its gate is `GatedChoice.softGate` on `chargedScore = P₁.scoreR − ϖ · pS`, with
`pS = (price of the date's sentence, 0)`, and `P₁`'s preference, `τ`, `δ`.

**Theorem** (`same_question_two_realizations`, registered
`scoreside.same-question-two-realizations`). For every `O`, every `v` with `Assessed O v`, every
`ϖ ≥ 0` with `ϖ · WB.market DP 4 (O.shortfall 4) ≤ 19/240`:

1. the run's own gate acts with mass `≥ 24/25` at date `4` and refrains with certainty at
   date `9` (`WarrantInductorRebuttal.same_question`);
2. the score-side gate acts with mass `≥ 24/25` at date `4` (`before`) and refrains with
   certainty at date `9` (`after`, for every `ϖ ≥ 0`);
3. `v.Holds (O.shortfall 4)` and `v.Holds (O.shortfall 9)`: acting is assessed a shortfall at
   both dates.

Beside it: `bundle_unchanged` and `market_unchanged` (`rfl`: `scoreSide` stores `WB`, so these
are design facts, not results), `no_conduct_row` (the one row *refrain* was compiled to,
`conductRow = ⟨e_{XAY}, 1/3⟩`, is held at no date, by the constants of the held rows:
`bundle_row_b_ne`), `scoreGate_zero` (at `ϖ = 0` the two gates coincide), `override` (if
`ϖ · price ≥ scoreR(act) − τ` the act's weight is `0`).

**Necessity** (`strength_row_necessary`). `p₀ = (1, 3/4, 0, 0, 3/4)`: `InCube p₀`; every row of
`(NB 4).bundle` other than the specialized strength row `rowS4` is satisfied at `p₀`
(`p₀_sat_without_strength`); `rowS4` is violated there (`p₀_violates_strength`); and for every
`κ ≥ 0`, `gateAt p₀ κ 0 = 0` and `gateAt p₀ κ 1 = 1`, where `gateAt p κ` is the charged gate at
the price vector `p` with charge `κ` on acting and `scoreGate_eq_gateAt` says
`scoreGate (scoreSide O ϖ) n = gateAt (WB.priceVec DP n) (ϖ · price)`. The bundle without the
strength row is a weaker hypothesis package, satisfied by a point at which the decision differs.

**Theorem** (`conduct_on_prices_conflicts`, registered
`scoreside.conduct-on-prices-conflicts`). `¬ ∃ x, ((NB 4).bundle ++ [conductRow]).Region x`,
by the certificate `conductCert = (1 · rowS4, 2/3 · rowA4, 1 · conductRow)` with constant
`−1/6`, through `conflict_sound`. And `conduct_on_prices_idle`: every point of `(NB 9).region`
satisfies `conductRow`. This is the chosen compilation of *refrain*.

**Hypotheses.** `before`: `Assessed O v` and the charge bound `19/240`, which is
`(1/2 − 1/240) − 5/12`, the room the enforced strength and applicability rows
(`excess ≤ 1/400`) leave above `τ + δ`. `after`: `Assessed O v`, `0 ≤ ϖ`. Everything else is the
run's (`inductor`'s conformance at enforced dates, `memS4`, `memA4`, `memA9`, `memPin9`).

**What inhabits it.** Any `O`, any `v` making every `O.shortfall n` true (then `Assessed O v`,
since `ShortfallAt n` holds at every date), and any `0 ≤ ϖ ≤ 19/240` — the bound is met at every
market, prices lying in `[0, 1]`; at `ϖ = 0` the gate is the run's.

**What is typed.** `Assessed`: no assessment process settles the sentences in Lean; their
generability; whether the market prices them well. Which row *refrain* compiles to.

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
between `WarrantForce`'s calibrated day value — whose positions vanish when a row is satisfied —
and a unit position per instance; timeliness is the shape of the data (`consequent : ℕ → Bool`).
**The same theorem elsewhere.** `DecisionComponent.bounded_iff_not_outperformed` with
`h := realized`, `g := held`; this is that theorem renamed, not new mathematics.

**Theorem** (`suspect_in_bundle`, registered `solvency.conflict-names-suspects`). For a bundle
`B`, a `FarkasCert` whose rows are `B.Allowed`, and `x ∈ InCube`: some `i` with `0 < mult i`
has `row i` a row of `B` and `¬ (row i).Sat x`. The `i` depends on `x`: at every cube point some
positively weighted bundle row is violated there, and no single row is shown violated everywhere.
From `exists_violated_suspect` (every certificate, every `x`, no cube hypothesis). Corollaries:
`no_conflict_of_sound` (rows all valid at one point admit no valid certificate),
`unique_suspect`, `suspect_in_normState`.

**Hypotheses.** The certificate's rows are allowed rows of the bundle (the compile's `Valid`
condition for a `conflict` result); `x` in the cube. **Typed.** Which point is "the true
posterior"; whether admission demands validity at it — without that premise a conflict is not
shown to be a mis-admission. Solvency is not what excludes a certificate: two contradictory rows
each enforced on one instance have bounded cumulative liability.

## 3. The robust reading on the eight-world model (`RobustWarrant`)

**Setting.** Worlds `Bool × Bool × Bool` (quantity, signal, challenge); `μ` the product
measure (uniform prior, signal accuracy `3/4`, challenge accuracy `2/3`). `Aev` the signal
true, `Yev` the quantity true, `Cev` the challenge contrary, `Ccev` concurring.
`Robust μ A Y c U := ∀ E ∈ U, 0 < μ(A∩E) → c · μ(A∩E) ≤ μ(A∩Y∩E)`;
`robustStrength` the least `μ(A∩Y∩E)/μ(A∩E)` over `E ∈ U` with `A∩E` possible.
`Uall = {univ, Cev, Ccev}`, `Udef = {univ, Ccev}`: declared extension sets.

**Theorem** (`robustStrength_both`, registered `robust.eight-world-strengths`).
`robustStrength μ Aev Yev Uall _ = 3/5 ∧ robustStrength μ Aev Yev Udef _ = 3/4`
(`robustStrength_all`, `robustStrength_defeated`). Beside it: `robust_all_iff`,
`robust_defeated_iff`, `against_robust_iff` (the opposing warrant's strength is `2/5`);
`robust_meet` (`3/5 ≤ y ∧ 2/5 ≤ 1 − y ↔ y = 3/5`); `robust_sound` (a robust warrant's row is
valid at every record of `U` with positive mass at which the anchor is possible);
`valid_at_signal` (the row at the record `univ`), `invalid_at_contrary` (at `Cev`);
`posterior_signal`, `posterior_contrary`, `posterior_concurring`; on the three-coordinate
embedding `kept_under_challenge`, `not_undercut`, `survives_challenge`
(`[occ].survivors quiet Fch = [occ]`: the grounded survivor rule keeps the warrant at the
challenge record), `contributed_row_invalid`; `naiveCert`, `naive_conflict`.

**Hypotheses.** None beyond the stated model. **Inhabitants.** The model itself; `mass_univ`.
**Typed.** The extension sets: `Uall` and `Udef` are inputs, and no theorem derives either from
`Grounds.survivors`, `settleForm` or `undercut`; "the contrary challenge declared a defeater" is
the choice of `Udef`. **What would make it vacuous.** An empty extension set, excluded by
`Uall_nonempty`, `Udef_nonempty`. **The same theorem elsewhere.** None; the eight-world model
is not exposed in Lean elsewhere (`ThinLegitimacy` §11 mentions one in prose). **Not shown.** Any
`Form`-level rule or compile of the robust reading, or any defeat semantics (item 133).

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

**The witness.** `start₁ = ⟨[0], {1}, 1, _⟩` exposes obligation `1` alone;
`initialS₁ : Initial protocolS₁ anchor start₁` (admission of `1` by `J₁`, which leaves matter `1`
with the agent); `stateS₁ = initialS₁.state`; `entitlementS₁ : Entitlement stateS₁ grounds
(fun _ _ => True)` with `origin _ := 1`, admitted under `J₁`, account live (`account_live₁`),
`Expresses` total. `witness_origin o ho : entitlementS₁.origin o ≠ 0` is the theorem at it.
`Initial` admits every exposed occurrence and obligation `0` is admitted at no history under
`J₁`, so every `Initial` over `protocolS₁` exposes obligation `1` alone.

**Hypotheses.** The entitlement's own fields; the allocation is constant in the history at the
fixture (`fun _ => J₀`, `fun _ => J₁`), a history-dependent allocation being the general case
the definition takes. **Typed.** `Expresses` (total at both fixtures). **The same theorem
elsewhere.** `WarrantInductorWitness.answered_not_entitled`, with the account's fate replaced
by the allocation's holder. **Not shown.** Anything about `authorized` against the account (item
128(b)); entitlement along an evolution (128(c)); the `Expresses` half of 128(a).
