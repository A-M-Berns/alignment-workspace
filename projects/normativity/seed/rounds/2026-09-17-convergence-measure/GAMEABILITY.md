# Gameability

Five attacks on the naive profile, each run as a fixture (`src/fixtures.py`,
`tests/test_measure.py`), and what blocks each.

## 1. Fragment dilution — succeeds against the naive average; blocked

Fixture `dilution`: one coordinate in discord (`[1/5, 1]` against `[0, 4/5]`, hull width
`1`) and three coordinates pinned by the world.

| `Φ` | naive `hullSum / |Φ|` | blocked `hullSum / |unpinned Φ|` |
|---|---|---|
| `{φ}` | `1` | `1` |
| `{φ, p₁, p₂, p₃}` | `1/4` | `1` |

Lean: `naiveHull_insert_pinned_le` (adding a pinned coordinate lowers the naive
average) and `blockedHull_insert_pinned` (the blocked average is unchanged).  Two
declarations block the attack: `Φ` is declared, so nobody adds to it; and the blocked
normalization ignores pinned coordinates outright, so even a declared `Φ` padded with
pinned sentences reads the same.  The blocked version is the one to quote.  With
declared weights the block is the same statement: weights on pinned coordinates are
wasted mass, and a declaration that spends mass there has diluted itself in the open.

## 2. Coordinate splitting — succeeds against a refined fragment; blocked by pull-back

Fixture `splitting`: `p` with intervals `[3/5, 1]` and `[0, 2/5]` (discord); `p` refined
into exclusive `p₁, p₂` with the coherence row `p = p₁ + p₂`, conservative transport.

| fragment | `Hull` | `Disc` |
|---|---|---|
| declared `{p}` before | `1` | `1` |
| declared `{p}` after refinement (pulled back to the disjunction coordinate) | `1` | `1` |
| refined `{p₁, p₂}`, inherited half-weights | `1` | `0` |

`Hull` happens to agree here; `Disc` does not: the discord on `p` is invisible on
`p₁` and `p₂`, each of which is free in `[0,1]` for both reasoners.  So the measure is
**not** transport-invariant on the refined fragment even with inherited weights, and the
failure is on the discord component.  The transport-invariant version is the one taken
on the **declared** fragment pulled back through `τ`: `Hull_Φ` after refinement is
`Σ_{φ∈Φ} w_φ |H_{τ(φ)}|`, and since conservative transport with fresh free refinements
leaves the interval of the disjunction coordinate unchanged (the refinement coordinates
occur only in the coherence row and can absorb any value), the profile on `Φ` is
unchanged.  The interval-invariance under fresh refinements is computed on the fixture
and argued, not Lean-stated (`REPORT.md`, not shown).

## 3. Agreement by vacuity — correct, and the reference profile

Two reasoners with empty substantive seeds have identical intervals, those of the closed
layer: `Disc = 0`, `Ovl = Hull = Hull(∅‑seeds)`.  The measure is **relative to the closed
layer**: every profile is read against the reference `Hull(∅‑seeds)` on the same `Φ`,
and what a pair of seeds has achieved is `Hull(∅‑seeds) − Hull(seeds)` at the cost of
`Disc(seeds)`.  On the moral fixture the reference is the third step's closed layer
(structure, coherence, settled valence at strength `9/10`): `Hull(∅‑seeds) = 7/12 + …`
is computed in `FIXTURES.md` §1.  No block is needed; the number is uninteresting and
says so.

## 4. Discord hiding — succeeds against either component alone; the profile is the target

Fixture `hiding`: against a narrow opposed reasoner, a reasoner holding only `[0,1]` has
profile `(1, 1/5, 0)`; a narrow one has `(1, 0, 1)`.  Holding wide intervals buys
`Disc = 0` at the price of `Hull = 1`; holding narrow ones buys nothing on `Hull` here
and pays `Disc = 1`.  Neither `Hull` nor `Disc` is a target; the pair is, in the
product order of `MEASURE.md` §2, and the hiding reasoner is not better in it.  The
theorem behind this is `overlapMass_anti` together with `discord_persists`: learning
lowers overlap and never removes discord, so a reasoner cannot improve its discord score
by narrowing and can only improve it by widening — which is what hiding is.

## 5. Weight capture — succeeds for reasoner-chosen weights; blocked by declaration

Fixture `weight_capture`: two coordinates, discord on the first.  With weight `ε` on it,
`Disc = ε`: `1/2`, `1/10`, `1/1000`.  A reasoner choosing its own weights zeroes its
discord in the limit.  Lean: `Weights d Φ` requires positivity, and
`discordMass_eq_zero_iff` says that under positive weights `Disc = 0` exactly when no
declared coordinate is in discord — the number a reasoner could drive down is bounded
away from zero by the declared minimum weight, and it cannot reach zero.  Weights are a
field of the shared constitutive declaration (`Weights` is a parameter of every mass,
never of a reasoner); the measure is not defined for reasoner-chosen weights in the same
sense that the seed's protected class is not chosen by the reasoner it protects.

## What is not blocked

- **Hidden discord** (`MANY.md` §2): a merged bundle can be infeasible with every
  declared common interval nonempty.  No declaration of `Φ` or `w` sees it; it is a
  limit of coordinate-wise measurement, and the certificate for it is the merged
  bundle's own `FarkasCert`.  Recorded in `COUNTERMODELS.md`.
- **Reference dependence** (§3): the profile compares seeds against a closed layer that
  is itself a declaration.  A different structural layer gives a different reference,
  and nothing here ranks references.
