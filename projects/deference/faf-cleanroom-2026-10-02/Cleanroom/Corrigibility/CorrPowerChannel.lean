import Cleanroom.Corrigibility.CorrPowerChannel.Power
import Cleanroom.Corrigibility.CorrPowerChannel.Evpi
import Cleanroom.Corrigibility.CorrPowerChannel.SelfCap
import Cleanroom.Corrigibility.CorrPowerChannel.J3
import Cleanroom.Corrigibility.CorrPowerChannel.Gap
import Cleanroom.Corrigibility.CorrPowerChannel.Separable
import Cleanroom.Corrigibility.CorrPowerChannel.Splice
import Cleanroom.Corrigibility.CorrPowerChannel.MetaBelief
import Cleanroom.Corrigibility.CorrPowerChannel.Orbit
import Cleanroom.Corrigibility.CorrPowerChannel.Mdp
import Cleanroom.Corrigibility.CorrPowerChannel.Channel
import Cleanroom.Corrigibility.CorrPowerChannel.Grip
import Cleanroom.Corrigibility.CorrPowerChannel.Hazard
import Cleanroom.Corrigibility.CorrPowerChannel.Witnesses
import Cleanroom.Corrigibility.CorrPowerChannel.LeaveOneOut

/-!
# `corr-power-channel`: EVPI, POWER, Turner's orbit theorems and the Channel package

Root module of the corrigibility area's home for the `power-wisdom`, `channel` and `d1` threads'
objects of record, over `corr-caution-power`'s carrier and FAF's `FactoredSpaces.Distr`:

* `Power` — T1: `mixValue`, `bestMix`, `attainable`, `power` (Turner Def. 5.1 one-shot), `evpi`
  (D12) with `evpi_nonneg` and the regret identity, `gainOf`, `reach`, `NonObstructive` (over a
  set of payoff functions), `regret`/`realizedHarm` against `V*` (no `ω*`), the caps, `voiExp`
  (D16, product form), `J3` and `J3Coverage` (D18).
* `Evpi` — T2: `voiExp_le_evpi`, `voiExp_nonneg` (Good), `j3_of_coverage`; E1 (`evpi_not_mono`
  against `power_mono`); the coarsened concentration ceiling and R1; D.4; average vs sup (A5/R4).
* `SelfCap` — T3: the inert per-option self-cap (`evpi_pair_null_eq_zero`,
  `evpi_insert_dominated`), A2, the support veto with R2's takeover cell and R3, low regret ⇒
  `θ`-slack non-obstruction and its refuted converse.
* `J3` — T4(a): the E3 family at `n + 1` plans with all closed forms, Blackwell monotonicity of
  `voiExp`, the legitimate channel `q`, and "J3 against asking first at every `n` iff `δ ≤ μh`".
* `Gap` — T4(b),(c): the takeover `J3 ⟺ P(Z) h_T > g` under both conventions; the
  structural-gap counterexample (the unrestricted inequality is false); D16's display refuted for
  a `ρ`-only `a` (`d16_display_fails_for_rho_only_a`, F-19).
* `Separable` — T4(b): the structural gap under additive separability, exact
  (`voiExp_marginal_sep_eq`: `VOI(s | q) = (EVPI₁ − VOI₁(q₁)) + EVPI₂`; the mandate's
  `voiExp_marginal_ge_rho` as `voiExp_marginal_ge_rho_sep`, with its content boundary
  `marginal_sep_perfect`/`marginal_sep_singleton`), the mandate's instance
  `δ(1 − 1/(n+1)) + σ(1 − 1/(m+1))` with the perfect scan (`e3rho_marginal`) and with the
  mandate's `(π, ρ)`-scan (`e3rho_marginal_piRho`), `VOI(k, perfect) = EVPI` for every `k`,
  `VOI(ofMap f) = EVPI` for every decision-sufficient `f` (`voiExp_ofMap_eq_evpi_of_factors`),
  and D16's display for the perfect scan by Blackwell (`marginal_perfect_antitone`).
* `Splice` — T5: `splice_bound`, `splice_alpha_bound` with (H1)–(H3) named, E4 realized,
  `unlock_iff` and its `corr-three-step` bridges (`unlock_iff_deltaMinus`, `unlock_iff_epsStar`),
  the R5 table.
* `MetaBelief` — T6: mean-only over a first-order posterior (E7); the meta-belief frame where the
  linear rule is not mean-only.
* `Orbit` — T7(a),(c),(d): the scaling law as an exact orbit count with the equality
  characterisation, the empty-or-`n!` dichotomy, and the equality for any `T` under an
  injective reward (`card_strictBestPerms_mul_of_injective`); `powerGrip_le_power` (erosion is
  POWER-seeking one-shot, every `D`, value-certain form) with strictness/equality; the mixture
  instantiation.
* `Mdp` — T7(b): the five-state MDP at `p = 1`, visit distributions, RSDs with the limit
  identity, average-optimality, Cor. 6.14 for `s_x = z` as `#erode ≥ 2·#keep` over the orbit
  (distinct rewards), the exact counts `40`/`80` of `120` (`cor614_orbit_count_exact`), and the
  tie-robust form for every reward (`cor614_orbit_count_strict`).
* `Channel` — T8: `Anticipation`, `(Mart)` as `ReflectiveFor`, `dataReach_eq_anticipated`, the
  barycentre converse (imported from `corr-general-object`), R2, Diaconis–Zabell per target,
  `SubstrateModel`/`ErodesReach`.
* `Grip` — T9: the affine grip value, informed and blind slopes with the Total-Trust
  characterisations and the two-state bridge, R1, keep-vs-erode, the S11 nine-cell grid.
* `Hazard` — T10: the component-hazard model, `margin_affine`, the exact thresholds
  `31603/894103` and `311795/1788206`, `λ* = 71737/80190`, pause stakes.
* `Witnesses` — T3's E3 instances (A1, R2); J3 over D18's full continuation set; the
  value-certain grip on R1's kernel (`powerGrip_r1_strict`); `splice_alpha_bound`'s full package
  inhabited on its boundary (`e4_reliable`, `e4_alpha_bound`) and in its interior
  (`e4_reliable_interior`, `e4_alpha_bound_interior`).
* `LeaveOneOut` — T11(a): the per-detector leave-one-out identity (d1 S7) for all four detectors and the four exact signs at the worked parameters.
-/
