import Cleanroom.Decision.DpWorldsJb.Defs
import Cleanroom.Decision.DpWorldsJb.Worlds
import Cleanroom.Decision.DpWorldsJb.JoinForm
import Cleanroom.Decision.DpWorldsJb.Sigma
import Cleanroom.Decision.DpWorldsJb.Annihilation
import Cleanroom.Decision.DpWorldsJb.Dyadic
import Cleanroom.Decision.DpWorldsJb.Countable
import Cleanroom.Decision.DpWorldsJb.JB
import Cleanroom.Decision.DpWorldsJb.Expressivity
import Cleanroom.Decision.DpWorldsJb.Gallow
import Cleanroom.Decision.DpWorldsJb.Bolker

/-!
# `Cleanroom.Decision.DpWorldsJb`: worlds, Stone spaces and Jeffrey–Bolker states

Root module of the `dp-worlds-jb` work package (faf-cleanroom run, 2026-09-29). The §0/§1 and
Appendix A record of [[decision-problems-v2]] over an abstract Boolean algebra, plus the
Jeffrey–Bolker material of the drafting chat and the 2024/2025 talk slides. Mathlib-only
closure (no FAF import: FAF has no Boolean-algebra worlds object).

* `Defs`: `Designation`, `World` (Definition 1), `Prob` (§1), `TwoValued`, `JBPair`,
  `JBPairTotal`, `JBState` (Definition 2), evaluators, `AgreesWithConditioning`.
* `Worlds`: **T1** `world_equiv_twoValuedProb`; the prime-filter bridge; **T5(a)** BPI
  existence and separation; **T5(b)** `worldEmptyEquivUltrafilter`, the hyperfilter world and
  `J₁`; **T5(c)** the finite–cofinite algebra.
* `JoinForm`: **T8(a)** `contJoin_iff_contMeet_compl`; the finite-sup lemma.
* `Sigma`: **T1(iv)** `prob_sigma_equiv`; **T7** `world_sigma_equiv_point`,
  `world_max_equiv_point`, `isLUB_val_eq_sUnion`; **T8(b)** `purely_atomic_of_singleton_designation`,
  Lebesgue excluded, `diracProb`; **T5(d)**.
* `Annihilation`: **T6** `no_world_of_halving`; `Dyadic`: its N+ `dyadic_no_world`;
  `Countable`: on a countable algebra the `Jω`-worlds are exactly the atoms
  (`worldJω_equiv_atoms`, `atomWorld`), so `no_world_of_countable_atomless` needs no measure
  and the dyadic witness is countable (`Dy.countable`, `dyadic_no_world_of_countable`).
* `JB`: **T4** `jbVec_equiv`, `jbVec_equiv_of_pos`, mixtures; the N− row
  `slide_vector_form_fails_at_v2_axiom` (v2 Definition 2's domain convention breaks the
  slide's vector form; under the slide's own convention the pair is not a JB structure,
  `slidePair_not_null_tolerant`); **T9**; **T2** atom determination.
* `Expressivity`: **T3** `rigid_eq_true_iff`, `rigid_faithful_iff_fibres_settle`,
  `coarse_smoking_lesion`.
* `Gallow`: **T10** `gallow_U2_eq_U3_of_imaging`, `gallow_U1_eq_U2_of_determinate`.
* `Bolker`: **S2** `bolkerTransform` (a linear map in vector coordinates), `bolker_preserves_order`,
  `probability_component_not_invariant`.
-/
