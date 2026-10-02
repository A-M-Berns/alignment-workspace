import Cleanroom.Deference.DefDoseResponse.Advisor

/-!
# Audit r3 (fidelity) probe — mesh-exactness on every steering day collapses `v` to `{0, 1}`

The hypothesis `hmesh : ∀ n < N, ∃ k ≤ n + 1, v = k/(n+1)` carried by
`quoteStream_steeredAdvisor_prefix`, `dose_graded_destination_steered`,
`cross_arm_audit_fires_steered` and the OPEN `twoWay_closure_exists` (with `0 < N`) is, at
`n = 0`, "`v = k/1` with `k ≤ 1`": day `0`'s mesh (FAF's `def:e` at precision `1`) is `{0, 1}`.
So for every `N ≥ 1` the "mesh-exact `v`" of those rows is `v ∈ {0, 1}` — not "any `v` whose
denominator divides `lcm(1, …, N)`" (`steeredAdvisor_quote_exact`'s docstring, F6), which at
`v = ½`, `N = 2` fails on day `0`. Machine-checked below. (The round-3 adversarial auditor's
probe `MeshExactCollapse.lean`, written in parallel, shows the same.)

Not imported by the library. Elaborate with `scripts/lean-check`.
-/

namespace Cleanroom.Deference.DefDoseResponse.AuditR3Fidelity

/-- At `N ≥ 1`, mesh-exactness on every day `< N` forces `v ∈ {0, 1}`. -/
theorem hmesh_forces_bool {N : ℕ} (hN : 0 < N) {v : ℚ}
    (hmesh : ∀ n < N, ∃ k ≤ n + 1, v = (k : ℚ) / ((n : ℚ) + 1)) : v = 0 ∨ v = 1 := by
  obtain ⟨k, hk, hv⟩ := hmesh 0 hN
  have hv' : v = (k : ℚ) := by simpa using hv
  interval_cases k
  · left; simpa using hv'
  · right; simpa using hv'

/-- The docstring's example class is wrong: `v = ½` has denominator dividing `lcm(1, 2) = 2`,
yet is not mesh-exact on every day `< 2`. -/
theorem half_not_mesh_exact_at_two :
    ¬ ∀ (n : ℕ), n < 2 → ∃ (k : ℕ), k ≤ n + 1 ∧ (1 / 2 : ℚ) = (k : ℚ) / ((n : ℚ) + 1) :=
    fun h => by
  rcases hmesh_forces_bool (v := (1 / 2 : ℚ)) (by norm_num : 0 < 2) h with h0 | h1
  · norm_num at h0
  · norm_num at h1

end Cleanroom.Deference.DefDoseResponse.AuditR3Fidelity
