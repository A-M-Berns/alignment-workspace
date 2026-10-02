import Cleanroom.Udt.UdtCondenseDd.Entropy

/-!
# Audit r3 (fidelity) probe: the per-atom form of `approxDD_entropy` with `I` on the right

Mandate T11(c) phrases the entropy-level approximate DD per atom ("`I[…] ≤ δ` as a hypothesis and
a bound on `|E[U | D_{I,B} = d] − E[U | Π̈ = [[d]]]|`"). The package ships the `D_{I,B}`-averaged
form (`approxDD_entropy`) and the per-atom form with the atom's own `KL_d` (`atom_bound`), and its
docstring says "the averaged form is what `I` alone bounds". This probe shows `I` alone *does*
bound each realized atom, at the price of the atom's mass:

`|E[U | d] − E[U | [[d]]]| ≤ √(I[E : D_{I,B} | Π̈] / (2 · P(d)))`

— one line from `atom_bound` and `P(d) · KL_d ≤ ∑_{d'} P(d') · KL_{d'} = I` (`condMutualInfo_eq_sum_mul_klFin`).
Not imported by the library.
-/

namespace Cleanroom.Udt.UdtCondenseDd.AuditR3

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset Cleanroom.Info

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE] [Fintype DE] [DecidableEq DE]
  [Fintype DI] [DecidableEq DI] [Fintype DB] [DecidableEq DB]
variable [MeasurableSpace OE] [MeasurableSingletonClass OE] [MeasurableSpace AE]
  [MeasurableSingletonClass AE] [MeasurableSpace DE] [MeasurableSingletonClass DE]
  [MeasurableSpace DI] [MeasurableSingletonClass DI] [MeasurableSpace DB]
  [MeasurableSingletonClass DB]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- Each summand of the bridge's right-hand side is non-negative (the argument inside
`approxDD_entropy_fin`, exported). -/
theorem mass_mul_klFin_nonneg (d : DI × DB) :
    0 ≤ mass S.μ.w (S.evDIB d) * InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) := by
  rcases eq_or_lt_of_le (mass_nonneg (fun ω => S.μ.nonneg ω) (S.evDIB d)) with h | h
  · rw [← h, zero_mul]
  · have hB := lt_of_lt_of_le h (mass_evDIB_le S d)
    exact mul_nonneg h.le
      (InfoVoiLatents.klFin_nonneg (condE_mem S d h) (condEz_mem S _ hB) (condE_absCont S d h))

/-- **Per-atom approximate DD with `I` on the right**: on a realized atom `d`,
`|E[U | d] − E[U | [[d]]]| ≤ √(I[E : D_{I,B} | Π̈] / (2 P(d)))`. -/
theorem atom_bound_condMutualInfo (hU : IsSubvariable S.E S.U) (d : DI × DB)
    (hd : 0 < mass S.μ.w (S.evDIB d)) :
    |condExpJunk S.μ.w S.U (S.evDIB d) (-1) - S.policyUtility (S.polOf d)| ≤
      Real.sqrt (I[S.E : S.DIB | S.polE ; dsMeasure S] / (2 * mass S.μ.w (S.evDIB d))) := by
  obtain ⟨u, hu⟩ := (isSubvariable_iff_exists S.E S.U).1 hU
  set u' : AE × DE → ℝ := fun e => max 0 (min 1 (u e)) with hu'def
  have hu' : ∀ ω, S.U ω = u' (S.E ω) := fun ω => by
    simp only [hu'def, ← hu ω]
    rw [min_eq_right (S.U_mem ω).2, max_eq_right (S.U_mem ω).1]
  have hu'01 : ∀ e, u' e ∈ Set.Icc (0 : ℝ) 1 := fun e =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have h2 : |condExpJunk S.μ.w S.U (S.evDIB d) (-1) - S.policyUtility (S.polOf d)| ≤
      Real.sqrt (InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) / 2) :=
    le_of_mul_le_mul_left (atom_bound S hu' hu'01 d) hd
  have h3 : mass S.μ.w (S.evDIB d) * InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) ≤
      I[S.E : S.DIB | S.polE ; dsMeasure S] := by
    rw [condMutualInfo_eq_sum_mul_klFin S]
    exact Finset.single_le_sum (fun d' _ => mass_mul_klFin_nonneg S d') (Finset.mem_univ d)
  have h4 : InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) / 2 ≤
      I[S.E : S.DIB | S.polE ; dsMeasure S] / (2 * mass S.μ.w (S.evDIB d)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    calc InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d)) * (2 * mass S.μ.w (S.evDIB d))
        = 2 * (mass S.μ.w (S.evDIB d) * InfoVoiLatents.klFin (condE S d) (condEz S (S.polOf d))) := by
          ring
      _ ≤ 2 * I[S.E : S.DIB | S.polE ; dsMeasure S] := by linarith
      _ = I[S.E : S.DIB | S.polE ; dsMeasure S] * 2 := by ring
  exact h2.trans (Real.sqrt_le_sqrt h4)

end

end Cleanroom.Udt.UdtCondenseDd.AuditR3
