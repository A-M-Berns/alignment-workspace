# The convergence measure

Lean: `lean/Workspace/Normativity/Contrib/ConvergenceMeasure.lean` §§1, 5, 7.  Executable:
`src/profile.py`.  Every name provisional.

## 1. Inputs

Reasoners `ι` (finite, nonempty) over one fragment of dimension `d`, one settlement `F`,
one structural and constitutive layer.  Reasoner `i` has a humble substantive seed
`Sⁱ_sub`, a live warrant set `Wⁱ` and a docket state, hence the forced region
`Kⁱ = K(Sⁱ ∪ Wⁱ, F)` and, for every coordinate `φ`, the forced interval
`Iⁱ_φ = [loⁱ_φ, hiⁱ_φ]` computed by the seed round's `forcedInterval`.  A reasoner whose
region is empty is refuted and has no intervals; the profile is taken over the reasoners
that have them, and the fixtures report who was dropped.

The Lean object is **interval data** `I : ι → Fin d → ℚ × ℚ` (`IntervalData`), with
`Valid I` saying each pair is a nonempty subinterval of `[0,1]`.  The theorems of §§1–3
and 6 are about interval data; §4 connects them to the regions.

A **declared fragment** `Φ : Finset (Fin d)` and **declared weights**
`Weights d Φ` — positive on `Φ`, summing to one — are constitutive-layer inputs.  In the
fixtures `Φ` is the set of ranking sentences (moral) or `{V, V₂}` (legal), and the
weights are uniform; neither was chosen after seeing a number.

## 2. The three masses

| object | definition | Lean |
|---|---|---|
| hull `H_φ` | `[min_i loⁱ_φ, max_i hiⁱ_φ]` | `hullLo`, `hullHi`, `hullWidth` |
| common interval `C_φ` | `[max_i loⁱ_φ, min_i hiⁱ_φ]`, empty when the lower end exceeds the upper | `commonLo`, `commonHi`, `commonWidth = max 0 (·)` |
| discord | `C_φ = ∅` | `Discord I φ := commonHi < commonLo`, decidable |
| hull mass | `Hull(Φ) = Σ_{φ∈Φ} w_φ |H_φ|` | `hullMass` |
| overlap mass | `Ovl(Φ) = Σ w_φ |C_φ|` | `overlapMass` |
| discord mass | `Disc(Φ) = Σ_{φ ∈ Δ} w_φ` | `discordMass` |

The **convergence profile** is `(Hull, Ovl, Disc)`.

**Orderings.**  Two are used and they are not one: the *hull order* (`Hull` down) and
the *discord order* (`Disc` down).  Neither alone is a target (`GAMEABILITY.md` §4): a
reasoner holding only `[0,1]` has `Disc = 0` and contributes width `1`; two narrow
opposed reasoners have small individual widths and `Disc = 1`.  A profile improves when
`Hull` does not rise and `Disc` does not rise, and strictly when one falls — the
product order on `(Hull, Disc)`.  `Ovl` is diagnostic: it says how much of the hull is
common ground, and it is **not** a target because it is nonincreasing under every
narrowing (`overlapMass_anti`) — a reasoner that learns loses overlap — so maximizing it
rewards ignorance.  It is kept because `Ovl = 0` with `Disc = 0` is the touching case
below, which the other two do not distinguish from disjointness.

## 3. Inequalities

| statement | Lean | status |
|---|---|---|
| `Ovl ≤ Hull` | `overlapMass_le_hullMass` | proved (`|C_φ| ≤ |H_φ|`, `commonWidth_le_hullWidth`) |
| `0 ≤ Hull ≤ 1` | `hullMass_nonneg`, `hullMass_le_one` | proved |
| `Disc = 0 ↔ ∀ φ ∈ Φ, ¬ Discord` | `discordMass_eq_zero_iff` | proved, needs positive weights |
| some declared `φ` in discord `→ Disc > 0` | `discordMass_pos` | proved |
| `Disc = 0 → Ovl > 0` on nontrivial `Φ` | `touching_refutes` | **false**: `[0, 1/2]` and `[1/2, 1]` touch at a point, no discord, common width `0` |

The prompt's third inequality fails because a common interval can be a point.  What is
true in its place: `Ovl > 0` implies some declared coordinate has a common interval of
positive width and is therefore not in discord, so `Ovl > 0 → Disc < 1`.

## 4. The pinned fragment

`pinned_lift` (from `seed_independence_strict`): if all reasoners share the closed layer
`B` and carry strict substantive layers with nonempty regions, then a coordinate pinned
by any one of them at `p` is pinned by all at `p`.  So on the fragment the closed layer
pins, every `H_φ` is a point, `|H_φ| = |C_φ| = 0`, and `φ ∉ Δ`.  The profile lives on the
unpinned fragment; this is what makes the blocked normalization of `GAMEABILITY.md` §1
the right one.

## 5. Relation to seed leverage

The seed round's *seed leverage* of one reasoner on `U` is `Levⁱ = Σ_{φ∈U} (1 − |Iⁱ_φ|)`.
Weighted, `Levⁱ_w = Σ w_φ (1 − |Iⁱ_φ|) = 1 − Σ w_φ |Iⁱ_φ|`.  For two reasoners, on each
coordinate, inclusion–exclusion on a line gives

    |H_φ| = |I¹_φ| + |I²_φ| − |C_φ|            if C_φ ≠ ∅
    |H_φ| = |I¹_φ| + |I²_φ| + gap_φ            if C_φ = ∅,  gap_φ = max lo − min hi > 0

so with `Gap(Φ) := Σ_{φ∈Δ} w_φ gap_φ`:

    Hull = (1 − Lev¹_w) + (1 − Lev²_w) − Ovl + Gap ,

that is, **shared narrowing** `1 − Hull = Lev¹_w + Lev²_w − 1 + Ovl − Gap`.  Two-reasoner
leverage therefore determines hull mass only together with the overlap and the discord
gap: two reasoners each with leverage `1/2` on one coordinate can have hull width `1/2`
(identical intervals), `1` (disjoint halves, `Ovl = 0`, `Gap = 0`) or anything between.
This identity is computed, not Lean-stated; the Lean carries the two inequalities it
rests on.  For `n > 2` reasoners the inclusion–exclusion has no such closed form, and
hull mass is not a function of the individual leverages at all.

## 6. Discord certificates

For `φ ∈ Δ` with two reasoners, say `hi²_φ < lo¹_φ`.  A lower-bound certificate
`c₁ : BoundCert d m₁ φ (−1)` over reasoner 1's bundle of value `−lo¹` and an upper-bound
certificate `c₂ : BoundCert d m₂ φ 1` over reasoner 2's bundle of value `hi²` merge
(`mergeCert`) into a `FarkasCert` for the concatenated bundle: coefficients cancel,
constant `hi² − lo¹ < 0`.  `discord_certificate`: the two forced regions have no common
point (through `conflict_sound` and `region_append_iff`).  The rows the certificate
weights positively, restricted to substantive and warrant rows, are what some reasoner
would have to give up; the fixtures compute them and a minimal such subset by the
deletion filter with the shared structural rows held fixed (`minimal_infeasible_items`).

**Existence.**  Given `φ ∈ Δ` the two bound certificates exist by LP duality — the
seed round's item 94 — and the fixtures find them by solving the dual feasibility
problem exactly.  Lean proves the merge and its soundness; it does not prove duality, so
"the certificate exists whenever `φ ∈ Δ`" is proved conditional on the two endpoint
certificates and computed unconditionally on every fixture.  For `n` reasoners the
same construction applies to the pair `discord_iff_pair` names (`MANY.md`).
