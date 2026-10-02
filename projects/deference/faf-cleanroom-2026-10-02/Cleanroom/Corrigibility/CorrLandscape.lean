import Cleanroom.Corrigibility.CorrLandscape.Map
import Cleanroom.Corrigibility.CorrLandscape.Trichotomy
import Cleanroom.Corrigibility.CorrLandscape.Regret
import Cleanroom.Corrigibility.CorrLandscape.Margin
import Cleanroom.Corrigibility.CorrLandscape.Kappa
import Cleanroom.Corrigibility.CorrLandscape.Crossing
import Cleanroom.Corrigibility.CorrLandscape.ActBased
import Cleanroom.Corrigibility.CorrLandscape.BasinToy
import Cleanroom.Corrigibility.CorrLandscape.Kalman
import Cleanroom.Corrigibility.CorrLandscape.Amplify
import Cleanroom.Corrigibility.CorrLandscape.Control
import Cleanroom.Corrigibility.CorrLandscape.Invariant
import Cleanroom.Corrigibility.CorrLandscape.Erosion
import Cleanroom.Corrigibility.CorrLandscape.Switch
import Cleanroom.Corrigibility.CorrLandscape.Timestep
import Cleanroom.Corrigibility.CorrLandscape.Selection
import Cleanroom.Corrigibility.CorrLandscape.Entrench
import Cleanroom.Corrigibility.CorrLandscape.Legitimizing
import Cleanroom.Corrigibility.CorrLandscape.TwoRound
import Cleanroom.Corrigibility.CorrLandscape.Drift
import Cleanroom.Corrigibility.CorrLandscape.Horizon

/-!
# `corr-landscape`: the approval lineage and the landscape map — root module

Run 2's `approval` thread (`approval-final.md`, S4–S12 with the adversary's repairs) and run 3's
`landscape` thread (`landscape-final.md`, D1a–D6′, Statements 1–7, Proposition R′, the dialogue's
additions), formalized over FAF's `Distr` in the finite shadow, in product form, **undiscounted
throughout** (the plan's discounted/undiscounted risk: no discount factor appears in this package).
Namespace `Cleanroom.Corrigibility.CorrLandscape`. Depends on `corr-trajectory` (its `oddsIneq`,
`Margin`, Layer F) and the parent `corr-three-step`; `Timestep` alone imports
`Cleanroom.Lit.LitShutdownPrefs` (outside the plan's dependency edge, recorded in the report).

The approval lineage (T1–T11):
* `Margin` (T1–T2): `effRates`, `effMargin`, `↔ oddsIneq` and `↔ Δ₋`, `= 0 ↔ ε*`; openness (kind T) and
  the robustness box by monotonicity.
* `Kappa` (T3): affine in `κ`, `m(0)`'s sign, `kappaStar` and the crossing, strict antitone in `ε`,
  `κ*(ε*) = 1` exactly, the P3′ table, `t_conf = 7`.
* `Crossing` (T4): `t* = 17` as a least index, failure from `17` on, the eventual bound, the four cells.
* `ActBased` (T5): `authIneq`, the consistent `p^A` and its floor, never-fails-iff-floor, the `t = 10`
  refutation row, drills (`epsStar_drill_le`, the `14, 13, 11` crossings), S14.
* `BasinToy` (T6): D9′ invariant, contraction with `ρ†`, outside, the separation pair, the D9 label
  refutation, the D4 bridge at hazard `0`.
* `Kalman` (T7), `Amplify` (T8), `Legitimizing` (T9: inert / legitimizing / delegitimizing with the
  null-update theorem and one instance each), `Control` (T10), `Invariant` (T11).
* `TwoRound` (E2(i)): the contraction's `Φ` is a Layer-F `IsSupermart` on the two-round product
  process (adapted + the step at every `t`), and not a potential. `Horizon` (E2(i), general horizon):
  `Φ` on `prodLaw T ν` with the prefix filtration is adapted (proved); its `SupermartStep` at `t < T` is
  the package's one **OPEN** statement (`Horizon.phiW_supermartStep`, F-21).
* `Drift` (E2(ii)): `|β_t − β_stat|` is **not** a potential for the fresh-draw kernel (refuted by a cell);
  the ℓ¹ deviation of the mass vector from `m_stat` is non-increasing, and controls `β`.

The landscape map (T12–T20):
* `Map` (T12–T13): the objects of record, Statements 1–2.
* `Trichotomy` (T14): the three identities, (a), (b), Toy T's cells.
* `Regret` (T15): Proposition R′, attained and approached tightness.
* `Erosion` (T16): check C, E2's stocks, (H-decay) exact, the switch's sufficient direction and the
  refuted iff, the `β_t` laws of motion.
* `Switch` (T17): worst-case scoring, the structural lemma, the exact two-signal rule (with the clause
  the mandate's closed form lacked), the cells, the grid finding.
* `Timestep` (T18: the TD agent's rule *derived* from its maximal choice, with `lit-shutdown-prefs`'s
  byproduct situation as the N+), `Selection` (T19), `Entrench` (T20).

Open: the `SupermartStep` form of the contraction over the general horizon-`T` product space (E2(i)
beyond two rounds, `Horizon.phiW_supermartStep`, diagnosis in F-21). Not formalized (text in the
findings): Gaussian noise, every Monte Carlo statistic.
-/
