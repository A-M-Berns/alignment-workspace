# Part C — the record of a market run

`Workspace.Normativity.Contrib.WarrantEntitlement`, section `RecordPart`; mirrored in
`src/record.py`.

## The objects

```
structure MarketRun (d) where
  grounds    : ℕ → Grounds d          -- the occurrences admitted, per date, with A1's provenance
  docket     : ℕ → DocketState        -- entry, defeat, withdrawal
  settlement : ℕ → Settlement d
  certs      : ℕ → List (ℕ × Bool)    -- certificate events: (event id, selected?)
  authorized : ℕ → Finset ℕ           -- the record's authorized events
  prices     : ℕ → Fin d → ℚ

structure RecordEntry (d) where
  state    : RecordState d            -- grounds, docket, settlement, authorized
  certs    : List (ℕ × Bool)
  position : Fin d → ℚ                -- the enforcer's position; no prices

abbrev Record (d) := ℕ → RecordEntry d
def trace (run : MarketRun d) (β : ℚ) : Record d
```

The position is the force algebra's `Σ_rows β · violation · normal` over the live bundle
(`positionOf`), equal to `TraderizedEnforcement.position` over the bundle's indices
(`positionOf_eq_position`). Prices enter the record through it and in no other way.

## The two non-vacuity lemmas, on the countermodel

Runs: `baseRun p` (the countermodel's two occurrences, quiet docket, no events, constant
price `p`) and `defeatRun` (docket `{1}` defeated).

- **Not injective** (`trace_not_injective`, `trace_not_injOn`): `baseRun (1/2) ≠ baseRun 1`
  and `trace (baseRun (1/2)) β = trace (baseRun 1) β` — both prices clear the row
  `P(φ) ≥ 1/2`, the violation is `0` at both, the position is `0` at both
  (`positionOf_base_eq_zero`), and nothing else in the run differs. So
  `ReasonMediatedAuthorship.reasonMediated_of_injOn` does not apply to the trace as a reason
  view: mediation by the record is not vacuous.
- **Not constant** (`trace_not_const`, `trace_not_constant`): the defeat shows in the record.
  So `reasonMediated_const_iff`'s isolated-principal reading does not apply either.
- The two payloads that make the point: the price `prices 0 0` is **not** reason-mediated by
  the trace on the audited class (`price_not_mediated`) — the record is strictly coarser than
  the run — while the docket **is** (`docket_mediated`). `position_nonzero` (in `Witness`)
  shows the record does carry the position when the price violates the row: at price `0`,
  `β = 1`, two duplicating rows, the position is `1`.

## `Licensed` from the record alone

`decideLicensed rec n φ v c event : Bool` and `decideLicensed_iff`: it decides
`Licensed (rec n).state φ v c event`. The record state is all it reads — grounds, docket,
settlement, authorized events — and `Licensed` is `Decidable` from the instances on
`Supported` (finite citation checks, rational comparisons, the two attained points checked
by the region's decision procedure) and `Finset` membership.

## What was not attempted, as instructed

Authorship over the record, transparency of the market run, and the inductor-as-principal
question. What Part C made visible is filed: the record mediates the docket and the position
but not the price, so the public defect `d_s = dist_∞(b_s, K_s)` of P2 — a price-derived
quantity — is not in the record either; whether it belongs there, and whether transparency
over a market run should be stated on the record or on the run, is item 116. The record's
`certs` and `authorized` fields are the carrier for item 115 (transport of `Licensed` across
record transitions).
