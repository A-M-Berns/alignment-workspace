# Countermodels

Everything that broke a candidate statement, numbered as the dispatch numbers the
attacks and pressure tests.  All in `src/fixtures.py`, asserted in `tests/`.

## Inequalities

- **`Disc = 0 → Ovl > 0` is false** (`touching`, Lean `touching_refutes`): `[0, 1/2]`
  against `[1/2, 1]`, profile `(1, 0, 0)`.  The common interval is a point.

## Gameability

- **1 Dilution succeeds against the naive average** (`dilution`, Lean
  `naiveHull_insert_pinned_le`): `1 → 1/4` by adding three pinned coordinates.
  Blocked: `blockedHull_insert_pinned`.
- **2 Splitting hides discord** (`splitting`): declared `{p}` has `Disc = 1`; the
  refined `{p₁, p₂}` with inherited half-weights has `Disc = 0` and the same `Hull`.
  Blocked by measuring on the declared fragment pulled back through `τ`.
- **4 Hiding**: `(1, 1/5, 0)` versus `(1, 0, 1)` — each component alone is gamed;
  the product order on `(Hull, Disc)` is not.
- **5 Weight capture**: `Disc = ε` for weight `ε` on the contested coordinate.  Blocked
  by positive declared weights, `discordMass_eq_zero_iff`.

## Dynamics

- **Discord is not dissolved by sharing** (`private_learning`): sharing the private
  warrant `P(φ) ≥ 3/5` with the reasoner holding `P(φ) ≤ 2/5` refutes that reasoner;
  the profile never returns to `(1, 1/10, 0)` by sharing, only by defeating the warrant.
  Lean: `discord_persists`.  Breaks the dispatch's "dissolved by sharing"; replaced by
  "removed by defeat or refutation".
- **Sharing a conflicting item refutes** (`moral_two.share_conflicting`,
  `population_private.shared_refuted`): the sum item shared into the prioritarian
  reasoner, and P1+P2 shared into the quality reasoner, each empty the receiver's region.
- **Hull oscillates under an infinite discovery class** (`oscillation_two`): widths
  `7/10, 1, 7/10, 1, …`.  Breaks H2 without summability.

## Many reasoners

- **Hidden discord, two reasoners** (`hidden_discord.two`): `Disc = 0`, profile
  `(1, 1/4, 0)`, merged bundle infeasible, item subset `{y ≥ (9/10)x, x ≥ 4/5, y ≤ 3/10}`.
  Breaks "`Disc = 0` iff the merged bundle is feasible" in the forward direction.
- **Three-way discord with no pairwise discord** (`hidden_discord.three`):
  `x ≥ 3/5`, `y ≥ 3/5`, `y ≤ 1 − (9/10)x`; every pair of regions intersects, every
  common interval is `[3/5, 1]`, discord graph empty, triple infeasible.  Pairwise
  suffices for `Δ` (Helly) and not for merged feasibility.

## Fragility

- **Overlapping consensus breaks under a one-sided defeater** (`consensus`):
  `(1/3, 1/3, 0) → (1, 1/3, 0)` when one warrant on reasoner 1's docket is defeated.

## Not blocked by any declaration

Hidden discord.  It is a fact about coordinate-wise measurement and is certified only by
the merged bundle's `FarkasCert`; the report carries it under *what is not established*.
