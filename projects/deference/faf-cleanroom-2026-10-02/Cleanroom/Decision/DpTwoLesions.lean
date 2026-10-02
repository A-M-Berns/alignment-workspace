import Cleanroom.Decision.DpTwoLesions.Defs
import Cleanroom.Decision.DpTwoLesions.Laws
import Cleanroom.Decision.DpTwoLesions.FixedPoints
import Cleanroom.Decision.DpTwoLesions.Interior
import Cleanroom.Decision.DpTwoLesions.InteriorReal
import Cleanroom.Decision.DpTwoLesions.Corollary
import Cleanroom.Decision.DpTwoLesions.Ident
import Cleanroom.Decision.DpTwoLesions.PropD
import Cleanroom.Decision.DpTwoLesions.PropDWitness
import Cleanroom.Decision.DpTwoLesions.Lift
import Cleanroom.Decision.DpTwoLesions.CausalLearner
import Cleanroom.Decision.DpTwoLesions.MeanPolicy
import Cleanroom.Decision.DpTwoLesions.Presentation
import Cleanroom.Decision.DpTwoLesions.Recency
import Cleanroom.Decision.DpTwoLesions.Cumulative
import Cleanroom.Decision.DpTwoLesions.DeltaStar
import Cleanroom.Decision.DpTwoLesions.Coupled
import Cleanroom.Decision.DpTwoLesions.Indep
import Cleanroom.Decision.DpTwoLesions.DynWitness

/-!
# `dp-two-lesions`: the Two Lesions document and the instrumental-variable reading

Root module of the package `Cleanroom.Decision.DpTwoLesions` (area `decision`); no dependents
are planned. Files, each named after the mandate target it serves
([[dp-two-lesions-mandate]]):

* `Defs` — definitions of record (§3): `DlParams` (general `γ`, two grips), the worlds
  `(s, m, k)`, the `K`-generic coins and the label `procBoolK`, the `overwrite` and `bypass`
  trees, `nuP`/`VP`/`Delta`/`bestResp`/`IsFixedPt`/`fixedPts`/`HypH`, the instances `docP`,
  `sessP`, `withGrip`.
* `Laws` (T1) — the leaf sums and laws, the twelve world masses (`dlMass`) on both trees, the
  six cells and three observables from `nu`, the positivity of both conditioning events,
  `Delta_eq`, `oneLaw`, the strict monotonicity of the conditionals (the abstain one needs
  `δL < 1`).
* `FixedPoints` (T3) — `Δ(0)`, `Δ(1)`, the doc's two inequalities, Claim 1.1's iffs,
  Propositions 1–2, (H) at the doc's parameters, the scope witness at the session's.
* `Interior` (T4, any ordered field) — the quadratic of record, `signDelta`, the fixed-point set
  equality, Vieta, the factorisation and sign pattern, the regime criterion's `⇒` half and its
  `⇐` engine given a square root.
* `InteriorReal` (T4 over `ℝ`) — `prop3_three_iff`, `prop3_unique_iff` (IVT), `prop3_convex`,
  the instances `δ = 1/10, 1/100, 1/1000`.
* `Corollary` (T5) — the grip family explicit, `p̌(δ) → 0`, `p̂(δ) → 1`, the regime for all
  small `δ`, `Δ₀` derived as the pointwise limit, its unique fixed point `0`, the readings differ.
* `Ident` (T9) — identification from policy variation.
* `PropD` (T10, general) and `PropDWitness` (T10, the overwrite tree) — Proposition D(1) with
  the draw event, D(2), the overwrite witness, channel 3.
* `Lift` (T10(c), T11, T12) — the full-world tree carrying the draw and the tag; draw-recording
  for every `C`; the uncoupled IV estimands; Proposition 6; the per-protocol bias.
* `CausalLearner` (T13) — Proposition 7 (`rfl`), the policy value, the lab CDT, the §6 sentence
  refuted under the lab-CDT construal.
* `MeanPolicy` (T7), `Presentation` (T2), `Recency` (T6), `Cumulative` (T8, with Proposition 5
  refuted as stated by overshoot and repaired with a gap condition; the no-tie hypothesis
  discharged at `δ = 1/100`), `DeltaStar` (T20, the extension: `δ*` bracketed, the regime
  switching there, and `δ*` the unique root in `(0, 1/5)`).
* Repair round 1 (2026-10-01): `Coupled` (T11 — the coupled trees, compliance types, LATE, ATE,
  `ITT = κ·LATE`, `Wald = LATE`, Egan's variant reconstructed, the note's fractions; the coupling
  disclosed as (c) and shown to be a coupling of `overwriteFull`'s law), `Indep` (T3's Remark —
  the independent anti-lesion under both precedence conventions: `Δ(1) = 0` exactly under
  anti-first, of order `δ` under lesion-first), `DynWitness` (explicit trajectory witnesses for
  `prop4_fixedGrip`, `prop5_strong`, `prop5_weak_below`).
-/
