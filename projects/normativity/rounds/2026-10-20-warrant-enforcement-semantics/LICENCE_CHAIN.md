# Part A — the warrant as a provenance-carrying market object, and the licence chain

All declarations are in `Workspace.Normativity.Contrib.WarrantEntitlement`
(`lean/Workspace/Normativity/Contrib/WarrantEntitlement.lean`).

## A1. The typed warrant

```
structure Occurrence (d) where
  id        : ℕ                 -- the occurrence identity; also its docket port
  form      : Form d            -- premise X c | applicability X XA c | strength XA XAY c
  cites     : Applicability d   -- the applicability claim it cites: an occurrence, a settled coordinate, or none
  source    : Source            -- party p | settlement event
  defeaters : Finset ℕ          -- occurrences which, if live, undercut it
```

Each form compiles by the ported `Form.row` to a row `a · x ≤ b`: `premise X c` is
`P(X) ≥ c`, `applicability X XA c` is `P(X∧A) ≥ c·P(X)`, `strength XA XAY c` is
`P(X∧A∧Y) ≥ c·P(X∧A)` (`premise_sat_iff`, `applicability_sat_iff`, `strength_sat_iff`).
Grounds are a list of occurrences; `Grounds.seed` presents them as the seed's substantive
items on their own ports, and `Grounds.region st F` is the ported `forcedRegion` of that
seed under a docket `st` and a settlement `F`. `Grounds.region_iff` reads it by occurrence:
the cube, the settlement's pins, and the row of every occurrence whose port the docket has
not defeated. `Grounds.mem_bundle_iff` reads the live bundle the same way, by citation.

**What the defeat set does not yet do.** `Grounds.region` consults the docket's defeated
ports only; `defeaters` and `cites` are carried as provenance and not consumed by the
compiler. That is the branch's model (per-row ports) and it is what produces the orphan pin
of `COUNTERMODELS.md` §3. Item 112 is the compiler rule that consumes them.

> **2026-10-22.** The rule landed: `Grounds.survivors` consumes `cites` and `defeaters`
> (`WarrantEntitlement.mem_survivors`), and `Supported` reads the settled bundle rather than
> `Grounds.bundle`. `Grounds.region` is kept as the comparison object of the countermodels.

## A2. The chain

A verdict is a value `v : ℚ` for a coordinate `φ`.

- `Admissible G st F φ v` — some point of the region gives `φ` the value `v`.
- `VerdictCert d m m' φ` — a lower `BoundCert d m φ (−1)` and an upper `BoundCert d m' φ 1`,
  a citation `Cite d` for every row of each, and two points `loPoint`, `hiPoint`.
  `CitesLive c B`: every positively weighted row is admitted into the bundle **under its
  citation** (`RowAdmitted B q r`: `⟨q, r⟩ ∈ B`, or `r` is a cube face), on both sides.
- `Supported G st F φ v c` — `c.CitesLive (G.bundle st F)`, `−c.lo.value ≤ v ≤ c.hi.value`,
  and the two points lie in the region and attain the two endpoints.
- `RecordState d` — grounds, docket, settlement, and the finite set of authorized events.
- `Licensed R φ v c event` — `Supported` on `R`'s grounds, docket and settlement, and
  `event ∈ R.authorized`.

Theorems: `licensed_supported`, `supported_admissible` (by `region_convex` — `Bundle.Region`
is convex over `ℚ` — and `region_attains_between`), `licence_chain`. `Supported.valid`: the
endpoints of a supported certificate are valid bounds on the region (`BoundCert.sound_of_pos`
needs the rows only where the multiplier is positive). Every predicate is `Decidable`
(`decideLicensed_iff` in Part C).

Where the decisions sit: `Admissible` and `Supported` are the compiler's — region
membership and a certificate check; `Licensed` adds the two facts only a record has, the
docket (which citations are live) and the authorization of the issuing event. That is P1's
"the compiler decides the first two; the record decides the third", and it is a theorem
here only because `Supported` cites **by occurrence**: `Allowed` (the compiler's own notion
on `Bundle`) admits a row by its *value*, and under it A3's stale certificate would pass.

## A3. Admissible does not imply Supported (`Countermodel`)

One coordinate. `r₁ = ⟨1, premise 0 (1/2), none, party 1, ∅⟩`,
`r₂ = ⟨2, premise 0 (1/2), none, party 2, ∅⟩`, `G = [r₁, r₂]`, empty settlement. The region
is `[1/2, 1]` on `φ` under the quiet docket and under `stDefeat = ⟨{1}, ∅⟩`
(`region_iff`, `region_unchanged`). `cert k` cites occurrence `k` for its lower row (the
premise row specialized by the empty settlement, multiplier `1`, value `−1/2`) and the cube
face `x 0 ≤ 1` for its upper row; `loPoint = 1/2`, `hiPoint = 1`.

- `supported_quiet k`: for `k ∈ {1, 2}` and any `v ∈ [1/2, 1]`, supported on the quiet docket.
- `stale_not_supported`: after the defeat of `r₁`, `cert 1` is not supported — its one
  positively weighted lower row is cited into a bundle that carries `⟨Cite.sub 2, row⟩` but
  not `⟨Cite.sub 1, row⟩`, and the row is no cube face.
- `fresh_supported`: `cert 2` is supported after the defeat.
- `admissible_not_supported`: `Admissible G stDefeat F φ (1/2) ∧ ¬Supported … (cert 1) ∧
  Supported … (cert 2)`.

This is the countermodel to any licence that depends only on the region: the region did
not move, and the licence must still be refused. The transport half of item 56 follows the
same shape — a licence survives a record transition exactly when its cited occurrences do —
and is filed as item 115.

## A4. Supported does not imply Licensed

The region `[1/2, 1]` has `a = 1/2 < b = 1` (`forcedInterval : IsForcedInterval … (1/2) 1`).
Verdicts `2/3` and `3/4` are both inside and both supported by `cert 1`. `recordAuth`
authorizes event `7`; `recordNoAuth` authorizes nothing. `supported_not_licensed`: both
supported, `Licensed recordAuth φ (2/3) (cert 1) 7`, `¬Licensed recordNoAuth φ (3/4) (cert 1) 7`.

Whether the selection is licensed is a transparency fact of the record. `selection_not_transparent`
is the instance of `GateIsLegitimacy.tiebreak_transparency`: `TraceInterface Bool Party ℚ`
with the advisor entering the selected verdict at event `0`; `TFrame Bool Unit Bool Unit Bool ℚ`
whose two continuations enter the same declared inputs (`x` constant) and differ in the
advisor's contribution (`2/3` against `3/4`); for every declared reference `κ`,
`¬TransparentAt interface frame κ 0`. Not re-proved; applied.

## What Part A does not do

It does not say which occurrences a certificate *must* cite beyond its positively weighted
rows, does not make the defeat set operative, and does not state transport. Those are item
56's remainder, now items 112 and 115.
