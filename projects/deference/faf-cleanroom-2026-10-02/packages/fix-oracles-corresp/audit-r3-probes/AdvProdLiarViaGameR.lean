import Cleanroom.Fixpoint.FixOraclesCorresp.BrouwerOnly

/-!
# Audit round 3 (adversarial) probe: does the `prodLiar` witness really "apply verbatim" to the
Brouwer-only existence theorem?

Not imported by the library. The ledger row for `exists_reflectiveOn_via_gameR_brouwer` says its
witness is "`gameR_prodLiar_forces_main_one` / `_zero` apply verbatim to the equilibrium produced".
This probe checks that claim mechanically: instantiate the existence theorem on `prodLiarC`,
`prodLiarD`, `R = {0}`, `B = 1`, thresholds `p ∈ (0, 1)`, and read off the vector it produces —
`![1 − p, 1]` under the prescription `x₀ = ![0, 1]`, `![1, 0]` under `x₀ = ![0, 0]`. So the
Brouwer-only theorem's conclusion is inhabited by a hand-checkable vector, and the prescription off
`R` changes the answer forced on `R`, on the very statement the row is about (not only on
`gameR_nash_reflectiveOn`).
-/

namespace AdvProdLiarViaGameRProbe

open Cleanroom.Fixpoint.FixOraclesCorresp Set StrategicGame

/-- Prescription `x₀ 1 = 1`: the Brouwer-only theorem produces `![1 − p, 1]`. -/
theorem viaGameR_brouwer_prodLiar_one {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ x : Fin 2 → ℝ, x ∈ cube (Fin 2) ∧ x 0 = 1 - p ∧ x 1 = 1 ∧
      ReflectiveOn {0} (polyEv prodLiarC prodLiarD) (fun _ => p) x := by
  obtain ⟨σ, hσ, hcube, hoff, hR⟩ := exists_reflectiveOn_via_gameR_brouwer (B := 1) {0}
    prodLiarC prodLiarD prodLiarD_le (fun _ => p) (x₀ := ![0, 1])
    (fun i _ => by fin_cases i <;> simp)
  refine ⟨_, hcube, ?_, ?_, hR⟩
  · rw [extendBy_apply_of_mem _ _ (Finset.mem_singleton_self 0)]
    exact gameR_prodLiar_forces_main_one hp hσ _
  · rw [hoff 1 (by simp)]
    simp

/-- Prescription `x₀ 1 = 0`: the same theorem, same `c d R p`, produces `![1, 0]`. -/
theorem viaGameR_brouwer_prodLiar_zero {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ x : Fin 2 → ℝ, x ∈ cube (Fin 2) ∧ x 0 = 1 ∧ x 1 = 0 ∧
      ReflectiveOn {0} (polyEv prodLiarC prodLiarD) (fun _ => p) x := by
  obtain ⟨σ, hσ, hcube, hoff, hR⟩ := exists_reflectiveOn_via_gameR_brouwer (B := 1) {0}
    prodLiarC prodLiarD prodLiarD_le (fun _ => p) (x₀ := ![0, 0])
    (fun i _ => by fin_cases i <;> simp)
  refine ⟨_, hcube, ?_, ?_, hR⟩
  · rw [extendBy_apply_of_mem _ _ (Finset.mem_singleton_self 0)]
    exact gameR_prodLiar_forces_main_zero hp hσ _
  · rw [hoff 1 (by simp)]
    simp

/-- The `_one` vector is *not* globally reflective when `p > 1/2` (query `1` reads `x 0 = 1 − p < p`
and would need `x 1 = 0`): "reflective on `R`" is genuinely weaker than `Reflective` here. -/
theorem viaGameR_brouwer_prodLiar_one_not_reflective :
    ∃ x : Fin 2 → ℝ, x ∈ cube (Fin 2) ∧
      ReflectiveOn {0} (polyEv prodLiarC prodLiarD) (fun _ => (3 / 4 : ℝ)) x ∧
      ¬ Reflective (polyEv prodLiarC prodLiarD) (fun _ => (3 / 4 : ℝ)) x := by
  obtain ⟨x, hx, h0, h1, hR⟩ := viaGameR_brouwer_prodLiar_one (p := 3 / 4) (by norm_num)
  refine ⟨x, hx, hR, fun hr => ?_⟩
  have := (hr 1).2
  rw [polyEv_prodLiar] at this
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, h0, h1] at this
  norm_num at this

end AdvProdLiarViaGameRProbe
