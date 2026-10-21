# Confinement, grounded convergence, seed-independence

Lean: `SeedStatics.lean` §§7–8.  Fixtures: `src/fixtures.py`, `src/defeat.py`.

## 1. C1, confinement — holds as a hull bound; the measure form is false

**Theorem (`confinement`, `confinement_forced`).**  If `lo₁ ≤ p₁ ≤ hi₁` and
`lo₂ ≤ p₂ ≤ hi₂` then `|p₁ − p₂| ≤ max hi₁ hi₂ − min lo₁ lo₂`.  With
`[lo_i, hi_i] = I_φ(Sⁱ ∪ W, F)` and `pⁱ = xⁱ φ` for `xⁱ ∈ K(Sⁱ ∪ W, F)`, this is C1 with
`|I¹ ∪ I²|` read as the **width of the convex hull**.  Immediate, as expected.

**The measure form is refuted (`measure_form_refuted`, `c1_measure_form`).**  Read as
the total length of the union, the bound fails whenever the intervals are disjoint:
`I¹ = [0, 1/10]`, `I² = [9/10, 1]` have union length `1/5` and admit prices `9/10`
apart.  Disjoint forced intervals on `φ` mean the two seeds are jointly infeasible on `φ`
— the common region is empty — so the measure form fails exactly where the "common
forced region" clause has nothing to say.

**Common region (`forcedRegion_merge`, `confinement_common`).**  The common region
`K(S¹ ∪ W, F) ∩ K(S² ∪ W, F)` is the forced region of the merged seed
`⟨S¹.sub ++ S².sub, str, con⟩` (same structural layer), and two prices both inside it
differ by at most the merged region's interval width — which can be strictly smaller
than the width of `I¹ ∩ I²`.

## 2. C2 — the landed calculus is a trace discipline, not a semantics

The landed defeat calculus is `DefeatTrace` with resolution kinds `answer`, `dispose G`,
`settle s` (`NormativeContinuity.lean` §5).  A disposal is admissible (`Answerable`) when
its grounds are **available** at the prefix — born strictly earlier, or settled (D1) —
it has a fresh successor carrying the load (D2), and someone other than the resolver
stands on the successor while some ground was opened by someone else (D3).  Nothing in
D1–D3 asks whether a ground is itself contested, undercut or vindicated.

Consequently the calculus **determines no extension**.  What it determines, for a given
trace, is:

1. the outstanding set at every prefix (`O n`) — which issues are live, hence which
   warrants' rows are in the forced bundle;
2. conservation: a disposed issue's load is on its successor, never gone (`carry`,
   `failure_conserves`);
3. admissibility of each disposal act, as a per-edge predicate.

Which disposals are *made* is the participants' act.  The fixture `defeat_calculus`
(`src/defeat.py`) has warrant `W`, undercutter `D1` of `W`, and undercutter `D2` of `D1`:

| object | value |
|---|---|
| grounded extension of the attack graph | `{W, D2}` (least fixed point of the characteristic function; unique) |
| preferred extensions | `{W, D2}` only |
| trace A: `D1` disposes `W`, then `D2` disposes `D1` | live `{W', D1', D2}` |
| trace B: `D2` raised first, then `D1` still disposes `W` (admissible: `D1` is available) | live `{W', D1, D2}` |
| trace C: everything raised, nobody disposes | live `{W, D1, D2}` |

All three traces are exhaustive in the prompt's sense (every warrant and defeater raised),
all are admissible, and their live sets differ from one another and from the grounded
extension.  Reinstatement does not exist: after `D2` disposes `D1`, `W`'s rows do not come
back — `W'` carries the *obligation to adjudicate the disposal*, not the endorsement; a
reassertion of `W` is a fresh issue.

**C2 becomes:** under exhaustive exchange the live warrant set is a function of the
shared trace, not of the warrant/defeater set; two reasoners sharing one docket share one
live set trivially, and two reasoners with separate dockets may end with different live
sets after raising the same items.  The grounded extension is definable on top
(`Graph.grounded`, the standard least fixed point on a finite graph, computed and unique
in the fixture) but is not what the landed calculus computes.  A **grounded-conformant**
trace — every disposal's grounds in the grounded extension, every warrant outside it
disposed — would make the live set equal the grounded extension; that is a hypothesis
one may impose on a trace, not a theorem of the calculus, and it is what C3 would need.

This is Finding 4 of the Horty check from the other side: the trace's future is not
recoverable from the attack structure, by design.

## 3. C3 — refuted under item-level humility

**Countermodel (`c3_refuted`, `sandwich`).**  Fragment `{φ, ¬φ}`, coherence
`P(φ) + P(¬φ) = 1`, `W = ∅`, quiet docket, empty settlement.

- `S¹_sub = { P(φ) ≥ 1/2 , P(¬φ) ≥ 1/2 }`, both strengths `1/2 ∈ (0,1)`: item-humble.
- `S²_sub = ∅`.

`I_φ(S¹) = [1/2, 1/2]` (a point); `I_φ(S²) = [0, 1]`.  The point is forced by the
substantive seed alone and leaves a trace on the forced fragment.  Item-level humility
does not prevent pinning because pinning is a *joint* property — two humble closed
halfspaces sandwich a coordinate — and no item-level condition sees it.  The same happens
with one humble item against a warrant: `W = {P(φ) ≤ 1/2}` and `S¹ = {P(φ) ≥ 1/2}`.

**What is true without further hypotheses** is one-directional (from
`forcedRegion_anti`'s shape applied to rows rather than settlement): a seed can only
*narrow* what `str ∪ W ∪ F` forces, so a point forced by the closed layer is forced by
every seed extending it, and a seed can add pins but never move one.  The trace a
substantive seed leaves is exactly the set of coordinates it pins beyond the closed
layer, and it is nonempty for humble seeds.

## 4. C3′ — seed-independence under strict humility, proved

Read a substantive endorsement `μ(g) ≥ 0` with strength `c < 1` as the **open** halfspace
`μ(g) > 0` — a humble item is one that is never active at a boundary.  Then:

**Theorem (`point_forced_of_open_layer`).**  Let `C ⊆ ℝ^d` be convex, `U` open,
`C ∩ U ≠ ∅`.  If `x φ = p` on `C ∩ U` then `x φ = p` on all of `C`.
*Proof.*  Take `y ∈ C ∩ U`, `z ∈ C`; the segment `y + t(z − y)` lies in `C` and, for small
`t > 0`, in `U`; its `φ`-coordinate is `p` there, so `z φ = y φ = p`.

**Corollary (`seed_independence_strict`).**  Two reasoners share a closed layer `B`
(structure, warrants, pins, cube; convex by `regionR_convex`) and carry strict
substantive layers `L₁`, `L₂` (open by `isOpen_strictLayer`).  If `K₁ = B ∩ L₁` is
nonempty and pins `φ` to `p`, then every point of `B`, hence every point of
`K₂ = B ∩ L₂`, has `x φ = p`.  The point-forced fragment and its values are those of the
closed layer; the substantive seed leaves no trace on them.

What the strict reading does to the sandwich: `P(φ) > 1/2` and `P(¬φ) > 1/2` have no
common point.  Fixture `strict_humility` (`src/fm.py`, which carries the strict flag the
Lean elimination tracks): closed layer `p ≤ q`, `q ≤ 1/2`; the closed item `p ≥ 1/2` pins
`p = q = 1/2`; the strict item `p > 1/2` makes the region empty.  So under strict
humility a substantive seed **narrows or breaks, and never pins**: its residue is open
or infeasible, the two kinds the moral fixture is asked to show.

Two remarks.  The enforcer projects onto closed regions, so the strict reading is a fact
about the *statics* (what is forced), not about what the enforcer holds; the closure of
`B ∩ L` is what it would enforce.  And an empty `K₂` is *refuted*, which is the
alternative to being pinned — the theorem is vacuous there and says so.

## 5. The five pressure tests

| # | fixture | result |
|---|---|---|
| 1 dogmatic item | `test_1_dogmatic_item`: `S¹ = {P(φ) ≥ 1}` | `I_φ(S¹) = [1,1]`, `I_φ(S²) = [0,1]`; the item is not item-humble (`c = 1`), and its pin is a closed row, so C3′ does not apply either: a permanent trace |
| 2 hysteresis | `hysteresis` | occurs; `STABILIZATION.md` §4 and `COUNTERMODELS.md` §2 |
| 3 refinement without transport | `refinement` | C3 fails through the structural layer: conservative `p₁ ∈ [0, 1/2]`, narrowing `p₁ = 1/2` (a pin), `p ∈ [1/2, 1]`; with both on `τ` the regions coincide |
| 4 price without reason convergence | `price_without_reason` | `I¹ = I² = [2/3, 1]` on `φ`, warrant ports disjoint (`{0,1}` vs `{2,3}`); confinement holds with zero gap and nothing about *why* has converged — the analogue of `Corrigible ∧ ¬Authored` |
| 5 disguise | `disguise`, `disguise_caught` | the level disguise `P(φ) = P(¬φ)` is caught (both coordinates pinned to `1/2`); the relational disguise is caught only against a declared symmetry (`SEED.md` §3) |

Test 3 is the one case where C3 fails **through the structural layer with identical
substantive seeds**: narrowing transport turns an equality between levels into a pin.
`τ` is therefore part of the closed layer's identity, not a convenience.
