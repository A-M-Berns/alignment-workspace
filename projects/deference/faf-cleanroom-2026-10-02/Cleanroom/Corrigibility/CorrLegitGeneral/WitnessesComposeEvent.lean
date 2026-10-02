import Cleanroom.Corrigibility.CorrLegitGeneral.WitnessesCompose

/-!
# corr-legit-general — T6(d): the event matters, and a `compose_value` instance

Repair round 2. (i) Findings F15 (T6(d), corr-wf13-2-062) said of the T6(c) frames that "no
choice of a smaller `L` restores the mixture there"; the package's own `cF2_legitimizingTT`
refutes that (audit r2 fidelity B1). The two facts are put side by side here, adopted from the
probe `audit-r2-probes/MixtureAtSmallerL.lean`: the mixture hypothesis at step one holds for
`L = {0, 1}` (`cF2_mixture_at_Lcomp`), and the composite holds conditional on `{0, 1}` while it
fails conditional on `Ω` (`cF3_composite_Lcomp_not_univ`). So on these frames the right event is
strictly smaller than `L₁₂ ∩ L₂₃ = Ω`: the intersection is not in general the event that
composes. (ii) `compose_value` (mm I7.1, `Compose.lean`) had no inhabiting instance (audit r2
adversarial N6): the normalized legitimate deferrer `(2/3, 1/3, 0)` on `F₂`/`F₃` gives one through
Theorem 2.2 (`compose_value_instance`), with the composite Value a fact the theorem produces,
while `π = (1/2, 1/4, 1/4)` itself does not value `F₃`.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

/-- **The mixture hypothesis at step one holds for the smaller event** `L = {0, 1}`: one
application of `mixture_of_legitimizingTT` to `cF2_legitimizingTT`. Findings F15's sentence "no
choice of a smaller `L` restores the mixture there" was false.
Source: [[legitimacy-general-final]] Statement 9(a) l. 67; corr-wf13-2-062; audit r2 fidelity B1
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem cF2_mixture_at_Lcomp : MixtureOfCands cF2 (restrict πc Lcomp) :=
  mixture_of_legitimizingTT (fun w => by fin_cases w <;> norm_num [πc, vec3_two])
    (by rw [comp_restrict.2.1]; norm_num) cF2_legitimizingTT

/-- **The composite holds conditional on `{0, 1}` and fails conditional on `Ω`** (even locally,
w.r.t. the two-cell question `{φ, ¬φ}`): the event that composes is strictly smaller than
`L₁₂ ∩ L₂₃ = Ω`.
Source: [[legitimacy-general-final]] Statement 9(c) l. 67, Proofs l. 142; corr-wf13-2-062; audit
r2 fidelity B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem cF3_composite_Lcomp_not_univ :
    LegitimizingTT πc cF3 Lcomp ∧ ¬ LegitimizingTT πc cF3 univ := by
  refine ⟨compose_positive_instance.2.2.2.2.2.1, ?_⟩
  intro h
  unfold LegitimizingTT at h
  rw [restrict_univ] at h
  exact cF3_not_totalTrustWrt (TotalTrust.wrt h _)

/-- The normalized legitimate deferrer `(2/3, 1/3, 0)` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem comp_norm_mem : (![2 / 3, 1 / 3, 0] : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Value at step one** for the normalized legitimate deferrer: `cF2_legitimizingTT` scaled
by `(mass π L)⁻¹` and converted by Theorem 2.2.
Source: [[mm]] I7.1 l. 164 (step-one hypothesis); this package
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem comp_value_step1 : Value ![2 / 3, 1 / 3, 0] cF2 := by
  have h := cF2_legitimizingTT
  unfold LegitimizingTT at h
  have hc : (0 : ℝ) < (mass πc Lcomp)⁻¹ := by rw [comp_restrict.2.1]; norm_num
  rw [← totalTrust_smul_iff hc, comp_restrict.2.2] at h
  exact (value_iff_totalTrust comp_norm_mem cF2).2 h

/-- **Value at step two** at both legitimate candidates `(3/4, 1/4, 0)` and `(1/2, 1/2, 0)`:
`cF2_cands_totalTrust` converted by Theorem 2.2.
Source: [[mm]] I7.1 l. 164 (step-two hypothesis); this package
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem comp_value_step2 : ∀ ρ ∈ cF2.cands ![2 / 3, 1 / 3, 0], Value ρ cF3 := by
  intro ρ hρ
  rw [cF2_cands_of_supp comp_supp.2] at hρ
  have hρ' : ρ ∈ cF2.cands πc := by rw [cF2_cands]; exact hρ
  have ht := cF2_cands_totalTrust ρ hρ'
  have hmem : ρ ∈ stdSimplex ℝ (Fin 3) := by
    simp only [mem_insert, mem_singleton] at hρ
    obtain ⟨⟨h0, h1, _⟩, _⟩ := cF_P
    rcases hρ with rfl | rfl
    · rw [← h0]; exact cF2.P_mem 0
    · rw [← h1]; exact cF2.P_mem 1
  exact (value_iff_totalTrust hmem cF3).2 ht

/-- **An inhabiting instance of `compose_value`** (audit r2 adversarial N6): the normalized
legitimate deferrer `(2/3, 1/3, 0)` is a distribution, values `F₂`, every one of its
`F₂`-candidates values `F₃` (`F₃` is not the Dirac frame: `compose_positive_instance`), and the
theorem yields `Value (2/3, 1/3, 0) F₃` — while the unconditioned `π = (1/2, 1/4, 1/4)` does not
value `F₃` (Theorem 2.2 and `cF3_not_totalTrustWrt`).
Source: [[mm]] I7.1 l. 164; corr-wf13-037; audit r2 adversarial N6
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem compose_value_instance : (![2 / 3, 1 / 3, 0] : Fin 3 → ℝ) ∈ stdSimplex ℝ (Fin 3) ∧
    Value ![2 / 3, 1 / 3, 0] cF2 ∧ (∀ ρ ∈ cF2.cands ![2 / 3, 1 / 3, 0], Value ρ cF3) ∧
    Value ![2 / 3, 1 / 3, 0] cF3 ∧ ¬ Value πc cF3 := by
  refine ⟨comp_norm_mem, comp_value_step1, comp_value_step2,
    compose_value comp_norm_mem comp_value_step1 comp_value_step2, fun h => ?_⟩
  have ht := (value_iff_totalTrust compose_counterexample.1 cF3).1 h
  exact cF3_not_totalTrustWrt (TotalTrust.wrt ht _)

end

end Cleanroom.Corrigibility.CorrLegitGeneral
