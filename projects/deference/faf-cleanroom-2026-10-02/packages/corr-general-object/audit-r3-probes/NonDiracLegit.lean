import Cleanroom.Corrigibility.CorrGeneralObject.PerQ

/-!
# Audit r3 (adversarial) probe — the T4 package with a *non-Dirac* target

The package's T4 witness `e2_legit_witness` has target `Q = δ_{(L,b)}`, and its push∩L is the
single world `(L,b)` (`e2_push_L_single` below), so `h_L` comes out as the value at one world.
This probe inhabits the *same* package — `IsOptimal`, `ValueLegit`, `FunLegit`, the two mass
guards, `0 < c_L`, both verdicts *through* `perQ_threshold`, `h_L` *through*
`harmOn_eq_of_valueLegit`, not endorsed — with a target spread over two worlds:

* worlds `(L,g) = 0, (L,b) = 1, (¬L,g) = 2, (¬L,b) = 3`, prior `e2P pL`, `L = e2L = {0, 1}`;
* kernel `k = (1/4, 3/4, 3/4, 1/4)`;
* target `Q = (1/4, 3/4, 0, 0) = P(· | E_Q, L)`; menu `e2V` (`cont = X = (1, −1, 1, −1)`, `stop = 0`);
* `h_L = E_Q[V stop − V cont] = 1/2` (a genuine average), `c_L = 1/2`, threshold `1/2`, `ℓ = pL`;
  comply at `pL = 4/5`, overrule at `2/5`; not endorsed (`ℓ < 1`).

Not imported by the library. Namespace `…AuditR3`.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject.AuditR3

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

/-- The package's E2 instance has a single world in push ∩ L. -/
theorem e2_push_L_single : e2L ∩ e2Press = {1} := by decide

/-- The non-Dirac kernel `(1/4, 3/4, 3/4, 1/4)`. -/
def ndK : Fin 4 → ℝ := ![1/4, 3/4, 3/4, 1/4]

theorem ndK_isKernel : IsKernel ndK := fun ω => by fin_cases ω <;> norm_num [ndK]

/-- The non-Dirac target `Q = (1/4, 3/4, 0, 0)`. -/
def ndQ : Distr (Fin 4) where
  mass := ![1/4, 3/4, 0, 0]
  nonneg i := by fin_cases i <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_four]; norm_num

theorem ndQ_two_worlds : ndQ.mass 0 = 1/4 ∧ ndQ.mass 1 = 3/4 := by
  constructor <;> simp [ndQ]

def ndS (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) : ThreeStep (Fin 4) Unit (Fin 2) :=
  toThreeStep (e2P pL h0 h1) ndK ndK_isKernel e2V {1} (singleton_nonempty _) ⟨0, by decide⟩

theorem ndQ_optimal : IsOptimal ndQ e2V 1 := by
  intro b; fin_cases b <;> simp [expect, ndQ, e2V, e2X, Fin.sum_univ_four] <;> norm_num

theorem ndQ_harm : expect ndQ (e2V 1 - e2V 0) = 1/2 := by
  simp [expect, ndQ, e2V, e2X, Fin.sum_univ_four] <;> norm_num

theorem nd_valueLegit (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) :
    ValueLegit (e2P pL h0 h1) ndK ndQ e2L (devVar e2V 1 0) := by
  rw [e2V_devVar]
  unfold ValueLegit
  simp [e2P, e2L, ndK, e2X, ndQ, expect, Fin.sum_univ_four] <;> ring

theorem nd_funLegit (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) :
    FunLegit (e2P pL h0 h1) ndK ndQ e2L := by
  intro ω
  fin_cases ω <;> simp [e2P, e2L, ndK, ndQ] <;> ring

theorem nd_guards_4_5 :
    0 < ∑ ω ∈ e2L, (e2P (4/5) (by norm_num) (by norm_num)).mass ω * ndK ω ∧
      0 < ∑ ω ∈ e2Lᶜ, (e2P (4/5) (by norm_num) (by norm_num)).mass ω * ndK ω := by
  rw [e2L_compl]
  constructor <;> simp [e2P, e2L, ndK] <;> norm_num

theorem nd_guards_2_5 :
    0 < ∑ ω ∈ e2L, (e2P (2/5) (by norm_num) (by norm_num)).mass ω * ndK ω ∧
      0 < ∑ ω ∈ e2Lᶜ, (e2P (2/5) (by norm_num) (by norm_num)).mass ω * ndK ω := by
  rw [e2L_compl]
  constructor <;> simp [e2P, e2L, ndK] <;> norm_num

theorem nd_gain_4_5 : (ndS (4/5) (by norm_num) (by norm_num)).gainOn () e2L (devVar e2V 1 0) = 1/2 := by
  rw [e2V_devVar]
  unfold ThreeStep.gainOn ndS
  rw [toThreeStep_pressExpectOn, toThreeStep_pressMassOn, e2L_compl]
  simp [e2P, ndK, e2X] <;> norm_num

theorem nd_gain_2_5 : (ndS (2/5) (by norm_num) (by norm_num)).gainOn () e2L (devVar e2V 1 0) = 1/2 := by
  rw [e2V_devVar]
  unfold ThreeStep.gainOn ndS
  rw [toThreeStep_pressExpectOn, toThreeStep_pressMassOn, e2L_compl]
  simp [e2P, ndK, e2X] <;> norm_num

theorem nd_frac_4_5 : (ndS (4/5) (by norm_num) (by norm_num)).pressFracOn () e2L = 4/5 := by
  unfold ThreeStep.pressFracOn ndS
  rw [toThreeStep_pressMassOn, toThreeStep_pressMass]
  simp [e2P, e2L, ndK, pushMass, Fin.sum_univ_four, Finset.sum_pair] <;> norm_num

theorem nd_frac_2_5 : (ndS (2/5) (by norm_num) (by norm_num)).pressFracOn () e2L = 2/5 := by
  unfold ThreeStep.pressFracOn ndS
  rw [toThreeStep_pressMassOn, toThreeStep_pressMass]
  simp [e2P, e2L, ndK, pushMass, Fin.sum_univ_four, Finset.sum_pair] <;> norm_num

/-- `h_L = 1/2` through `harmOn_eq_of_valueLegit`: a two-world average, not a point value. -/
theorem nd_harm_via_theorem :
    (ndS (4/5) (by norm_num) (by norm_num)).harmOn () e2L (devVar e2V 1 0) = 1/2 := by
  unfold ndS
  rw [harmOn_eq_of_valueLegit _ ndK_isKernel ndQ e2V {1} (singleton_nonempty _)
    ⟨0, by decide⟩ 1 0 e2L nd_guards_4_5.1 (nd_valueLegit _ _ _), ndQ_harm]

/-- Comply at `pL = 4/5`, through `perQ_threshold`. -/
theorem nd_comply :
    pushExpect (e2P (4/5) (by norm_num) (by norm_num)) ndK (devVar e2V 1 0) ≤ 0 := by
  have hc : 0 < (ndS (4/5) (by norm_num) (by norm_num)).gainOn () e2L (devVar e2V 1 0) := by
    rw [nd_gain_4_5]; norm_num
  have key := perQ_threshold (e2P (4/5) (by norm_num) (by norm_num)) ndK_isKernel ndQ e2V
    {1} (singleton_nonempty _) ⟨0, by decide⟩ ndQ_optimal 0 e2L nd_guards_4_5.1 nd_guards_4_5.2
    (nd_valueLegit _ _ _) hc
  rw [key]
  show complianceThreshold ((ndS (4/5) _ _).gainOn () e2L (devVar e2V 1 0)) _ ≤
    (ndS (4/5) _ _).pressFracOn () e2L
  rw [nd_gain_4_5, nd_frac_4_5, ndQ_harm]
  unfold complianceThreshold; norm_num

/-- Overrule at `pL = 2/5`, through `perQ_threshold`. -/
theorem nd_overrule :
    ¬ pushExpect (e2P (2/5) (by norm_num) (by norm_num)) ndK (devVar e2V 1 0) ≤ 0 := by
  have hc : 0 < (ndS (2/5) (by norm_num) (by norm_num)).gainOn () e2L (devVar e2V 1 0) := by
    rw [nd_gain_2_5]; norm_num
  have key := perQ_threshold (e2P (2/5) (by norm_num) (by norm_num)) ndK_isKernel ndQ e2V
    {1} (singleton_nonempty _) ⟨0, by decide⟩ ndQ_optimal 0 e2L nd_guards_2_5.1 nd_guards_2_5.2
    (nd_valueLegit _ _ _) hc
  rw [key]
  show ¬ complianceThreshold ((ndS (2/5) _ _).gainOn () e2L (devVar e2V 1 0)) _ ≤
    (ndS (2/5) _ _).pressFracOn () e2L
  rw [nd_gain_2_5, nd_frac_2_5, ndQ_harm]
  unfold complianceThreshold; norm_num

/-- Not endorsed (`ℓ = 4/5 < 1`), through `funLegit_endorsed_iff`. -/
theorem nd_not_endorsed : ¬ Endorsed (e2P (4/5) (by norm_num) (by norm_num)) ndK ndQ := by
  rw [funLegit_endorsed_iff _ ndK_isKernel.nonneg ndQ e2L (nd_funLegit _ _ _) nd_guards_4_5.1,
    e2L_compl]
  simp [e2P, ndK] <;> norm_num

/-- The full T4 package on a non-Dirac target. -/
theorem nonDirac_legit_package :
    ndQ.mass 0 = 1/4 ∧ ndQ.mass 1 = 3/4 ∧
      IsOptimal ndQ e2V 1 ∧
      ValueLegit (e2P (4/5) (by norm_num) (by norm_num)) ndK ndQ e2L (devVar e2V 1 0) ∧
      FunLegit (e2P (4/5) (by norm_num) (by norm_num)) ndK ndQ e2L ∧
      (ndS (4/5) (by norm_num) (by norm_num)).harmOn () e2L (devVar e2V 1 0) = 1/2 ∧
      (ndS (4/5) (by norm_num) (by norm_num)).gainOn () e2L (devVar e2V 1 0) = 1/2 ∧
      (ndS (4/5) (by norm_num) (by norm_num)).pressFracOn () e2L = 4/5 ∧
      pushExpect (e2P (4/5) (by norm_num) (by norm_num)) ndK (devVar e2V 1 0) ≤ 0 ∧
      ¬ pushExpect (e2P (2/5) (by norm_num) (by norm_num)) ndK (devVar e2V 1 0) ≤ 0 ∧
      ¬ Endorsed (e2P (4/5) (by norm_num) (by norm_num)) ndK ndQ :=
  ⟨ndQ_two_worlds.1, ndQ_two_worlds.2, ndQ_optimal, nd_valueLegit _ _ _, nd_funLegit _ _ _,
    nd_harm_via_theorem, nd_gain_4_5, nd_frac_4_5, nd_comply, nd_overrule, nd_not_endorsed⟩

end

end Cleanroom.Corrigibility.CorrGeneralObject.AuditR3
