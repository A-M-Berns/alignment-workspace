# Many reasoners

Lean: `ConvergenceMeasure.lean` §§1, 3 (`ι` arbitrary finite nonempty), §7.  Fixture:
`hidden_discord`.

## 1. The profile for `n` reasoners

Every definition of `MEASURE.md` is stated for a finite nonempty index type `ι`:
`H_φ` is the hull of all intervals (`inf'`/`sup'` over `univ`), `Δ` is where the common
intersection is empty, and the masses are the same sums.  The **discord graph** has an
edge `{i, j}` labelled `φ` when `Iⁱ_φ` and `Iʲ_φ` are disjoint (`discord_graph` in
`src/profile.py`).

**Helly in dimension one** (`discord_iff_pair`): `Discord I φ ↔ ∃ i j, hiʲ_φ < loⁱ_φ`.
The common intersection of intervals on a line is empty iff some pair is disjoint.
Hence:

- `φ ∈ Δ` iff the discord graph has an edge labelled `φ`;
- `Disc = 0` iff the graph is empty (`discordMass_eq_zero_iff` plus the above);
- every `φ ∈ Δ` has a **two-reasoner** certificate: the pair Helly names, merged by
  `discord_certificate`.  No `n`-way certificate is ever needed for *coordinate*
  discord.

## 2. What Helly does not give: hidden discord

The dispatch's third equivalence — `Disc = 0` iff the merged bundle is feasible on
`Φ` — holds in one direction only.  Merged feasibility gives a common point, hence a
common value on every coordinate, hence `Disc = 0`.  The converse fails, because
coordinate-wise intervals see projections and merged infeasibility can be relational:

**Two reasoners** (all items substantive, humble): reasoner 1 holds `y ≥ (9/10)x` and
`x ≥ (9/10)y`; reasoner 2 holds `x ≥ 4/5` and `y ≤ 3/10`.  Intervals: reasoner 1
`[0,1]` on both; reasoner 2 `x ∈ [4/5, 1]`, `y ∈ [0, 3/10]`.  Both common intervals are
nonempty, `Disc = 0`, and the merged bundle is infeasible (`x ≥ 4/5` forces
`y ≥ 18/25 > 3/10`), with a `FarkasCert` whose minimal item subset is
`{y ≥ (9/10)x, x ≥ 4/5, y ≤ 3/10}`.

**Three reasoners, no pairwise discord at the region level either**: `A: x ≥ 3/5`,
`B: y ≥ 3/5`, `C: y ≤ 1 − (9/10)x`.  Every pair of regions intersects, every common
interval is nonempty (`x, y ∈ [3/5, 1]`), the discord graph is empty, and the triple is
infeasible (`y ≤ 1 − 27/50 = 23/50 < 3/5`); the certificate names all three items.
So an `n`-way incompatibility with no pairwise incompatibility exists at the region
level, and it is invisible to the coordinate-wise profile.

**Consequences.**  Pairwise discord suffices for `Δ` (Helly) and does not suffice for
merged feasibility (the region is not a product of its projections).  The profile
measures *visible* incompatibility on the declared fragment; hidden discord is certified
only by the merged bundle's own `FarkasCert` (`merged_certificate`), which the fixtures
compute and which no choice of `Φ` or weights sees.  A profile with `Disc = 0` therefore
licenses "no declared sentence is contested", not "the reasoners could jointly hold
their bundles".  Recorded as the one attack on the measure no declaration blocks
(`GAMEABILITY.md`, `COUNTERMODELS.md`).
