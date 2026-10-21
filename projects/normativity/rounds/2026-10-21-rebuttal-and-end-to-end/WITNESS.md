# Part C — the end-to-end witness (item 35)

> **Superseded in part, 2026-10-22.** The survivor rule is now the grounded fixed point of `WarrantEntitlement.activeStep` (`mem_survivors`): the strength occurrence leaves at the undercut of the applicability it cites (`n₀`), not at the refutation of `Y` (`n_E`); retirement propagates along citation chains without a closure on the settlement. Where this document says the strength row is enforced through `[n₀, n_E)`, the Lean now says otherwise; the intervals and the bankroll constants are unchanged. See `../2026-10-22-normative-inductor-integration/REPORT.md`, *Repairs*.

Lean: `Workspace.Normativity.Contrib.EndToEndWitness` (`lean/Workspace/Normativity/Contrib/EndToEndWitness.lean`,
121 declarations audited). Exact rationals: `src/rebuttal.py::run_table`, `tests/test_rebuttal.py`.

## The fixture

| | |
|---|---|
| coordinates | `X = 0, X∧A = 1, X∧A∧Y = 2, Y = 3, Z = 4` (`Fixture2.X …`) |
| first warrant | `P(X) ≥ 4/5` (occurrence 1), `P(X∧A) ≥ 3/4 P(X)` (2, cites 1), `P(X∧A∧Y) ≥ 2/3 P(X∧A)` (3, cites 2, defeaters `{2}`) |
| second warrant | `P(Z) ≥ 1/2` (occurrence 4) |
| structural item | coherence `X∧A ≤ X`, strength 1 |
| constitutive layer | empty |
| odds | `4, 3, 2, 1`; `ρ = 4` |
| dates | `X` settles true at `n₁ = 3`; port `2` defeated at `n₀ = 5`; `Y` refuted at `n_E = 8` (with its closure `X∧A∧Y` false); nothing after |
| intensity | `β = 10` (not read by any bound) |

## The run

Intervals are `intervalAt n φ = forcedInterval (seedAt n) W quiet (settlementAt n) φ`, where
`seedAt n` and `W` are the survivors of the grounds under `settleForm` (`seedAt_eq_survivors`).
Each value is a theorem (`interval_XA`, `interval_XAY`, `interval_Z`) proved through the
elimination's correctness theorem, and the `#eval` lines at the end of the file run the
elimination executably; the two agree. Licence status is of the entry certificates
`certXAY` (cites 1, 2, 3) and `certZ n` (cites 4, re-issued at `n₀`).

| date | event | survivors | `I(X∧A)` | `I(X∧A∧Y)` | `I(Z)` | enforcer rows | reopening | `certXAY` | `certZ` |
|---|---|---|---|---|---|---|---|---|---|
| 0 | entry (C2) | 1, 2, 3, 4 | `[3/5, 1]` | `[2/5, 1]` | `[1/2, 1]` | P, A, S, Z | — | licensed (event 7) | licensed (event 7) |
| 1–2 | — | 1, 2, 3, 4 | `[3/5, 1]` | `[2/5, 1]` | `[1/2, 1]` | P, A, S, Z | — | licensed | licensed |
| 3 | `X` settles true (C4) | 1, 2, 3, 4 | `[3/4, 1]` | `[1/2, 1]` | `[1/2, 1]` | P, A, S, Z | none: nested per A4(a) | supported, rows specialized | supported |
| 4 | — | 1, 2, 3, 4 | `[3/4, 1]` | `[1/2, 1]` | `[1/2, 1]` | P, A, S, Z | — | | |
| 5 | port 2 defeated (C5) | 1, 3, 4 | `[0, 1]` | `[0, 1]` | `[1/2, 1]` | P, S, Z | by defeat (`defeat_widens`) | **not supported** (cites 2) | fresh `certZ 5` licensed (event 8) |
| 6–7 | — | 1, 3, 4 | `[0, 1]` | `[0, 1]` | `[1/2, 1]` | P, S, Z | — | | |
| 8 | `Y` refuted (C6) | 1, 4 | `[0, 1]` | `[0, 0]` | `[1/2, 1]` | P, Z | **{3} rebutted** | | licensed |
| 9, 10, … | nothing settles (C7) | 1, 4 | `[0, 1]` | `[0, 0]` | `[1/2, 1]` | P, Z | — | | licensed |

Enforcer position: zero at every date on the clearing price schedule `(1, a, a, a, z)` with
`a = 1` before `n_E` and `0` after (`clearing_mem`, `positionOf_eq_zero_of_region`) — which is
what makes two such schedules (`z = 1/2`, `z = 1`) give one record (`trace_not_injective`).

Hull mass over `{X∧A, X∧A∧Y, Z}` at weights `1/3` (`hullMass_run`): **`1/2, 1/2, 1/2, 5/12,
5/12, 5/6, 5/6, 5/6, 1/2, 1/2, …`** — falls at `n₁` (settlement, `hullMass_anti`), rises at
`n₀` (the undercut, `hullMass_mono`), falls at `n_E` (the pin on `X∧A∧Y`), constant from `n_E`
(`eventually_const`). Under the port-only rule the `X∧A` column reads `[0, 0]` from `n_E`
(`old_rule_pins`): the pin the rule prevents.

## The stage statements

- **C1** `seedC1_humble`: the seed is humble.
- **C2** `licensed_at_entry`; `decideLicensed_at_entry` through the record (`decideLicensed_iff`).
- **C3** `interval_XAY 0 = (2/5, 1)`, `interval_Z 0 = (1/2, 1)`; `rows5_eq` (the force
  presentation is the survivors through `toForceRow`); `liability_run` at `ρ = 4`.
  The bound on *`Y` itself* is `[0, 1]` at entry: the fragment of C1 has no coherence row
  tying `Y` to `X∧A∧Y`, so "the bound on `Y`" is read as the bound on the first warrant's
  conclusion coordinate `X∧A∧Y`. The reading is a correction to the prompt.
- **C4** `settlement_nests`: survivors unchanged, every interval nested, `Z` fixed.
- **C5** `undercut_widens` (`[3/4, 1] → [0, 1]`); `undercut_licences` (the certificate citing
  occurrence 2 fails `CitesLive`; a fresh `Z` certificate is licensed).
- **C6** `rebuttal_step`: `settleOutcome` of the strength occurrence is `rebutted` at `n_E` and
  `kept` at `n_E − 1`; `X∧A`'s interval is unchanged (widening `0`, the A4(b) bound attained);
  `X∧A∧Y` pinned; `Z` unchanged. `liability_run` covers the rebuttal with the two-witness
  bankroll. `old_rule_pins`: no orphan under the rule; the orphan under the old rule.
- **C7** `eventually_const` (`I n = I nE` for `n ≥ nE`), `docket_monotone`, `pinned_monotone`
  (the hypotheses of `eventually_const_of_finite`), `hullMass_run`, `trace_not_injective`,
  `trace_not_const`, `docket_mediated` (every audited class, every step).
- **C8** `witness`: the conjunction — humble ∧ both licensed ∧ `IsLogicalInductor` for the
  augmented market (via `inductor_run`, i.e. `conditional_normative_inductor` with
  `liability_run` and the computable-market and uptake hypotheses as that theorem takes them)
  ∧ `intervalAt n Z = (1/2, 1)` for `n ≥ nE` ∧ not injective ∧ not constant.

## What the witness does and does not show

It shows that every stage exists on `main` and composes in sequence on one fixture, with the
hand-offs typed: the rule produces the seed, the seed's region is what the elimination
reads, the survivors' rows are what the enforcer holds, the enforcer's liability is what the
Normative Inductor theorem consumes, and the record carries the docket. It does not show
computability of the augmented market or the uptake certificate (hypotheses, as in Theorem
7.2); does not run the market maker (positions are shown at clearing prices only); does not
evaluate the elimination in the kernel (`Rat` normalization does not reduce under `decide` —
the values are pinned by `forcedInterval_spec`, and run by `#eval`); and reports the single
reasoner `ι = Unit`, where hull mass is the sum of the widths and discord is undefined.
Nothing in this file is registered.
