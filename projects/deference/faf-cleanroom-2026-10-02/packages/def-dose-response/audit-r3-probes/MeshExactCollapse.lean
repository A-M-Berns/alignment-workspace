import Cleanroom.Deference.DefDoseResponse.Advisor

/-!
# Audit r3 (adversarial) probe — mesh-exactness on every steering day is `v ∈ {0, 1}`

Every composed `_steered` row (`dose_graded_destination_steered`, `cross_arm_audit_fires_steered`)
and the OPEN `twoWay_closure_exists` carry `hN : 0 < N` together with

  `hmesh : ∀ n < N, ∃ k ≤ n + 1, v = k / (n + 1)`.

FAF's day-`n` expectation has mesh `1/(n+1)`, so day `0`'s mesh is `{0, 1}`: with `0 < N` the
hypothesis package admits **exactly two targets**, `v = 0` and `v = 1`. The findings file (F6) and
the docstring of `steeredAdvisor_quote_exact` say instead that "`v`'s denominator must divide
`lcm(1, …, N)`" — false: the condition is that the denominator divides *every* `n + 1 ≤ N`, i.e.
`gcd(1, …, N) = 1`. Counterexample below: `v = ½`, `N = 2` (`2 ∣ lcm(1, 2)`), not exact at day `0`,
where the steered advisor quotes `1`. Two *consecutive* exact days already force `v ∈ {0, 1}`,
so the exposed-day form of the prefix hypothesis (carried in § Not done) does not escape this
unless the exposed steering days are never adjacent. Not imported by the library.
-/

namespace Cleanroom.Deference.DefDoseResponse.AuditR3

open Cleanroom.Deference.DefDoseResponse LogicalInduction

/-- With `0 < N`, mesh-exactness on every steering day forces `v ∈ {0, 1}` (day `0`'s mesh). -/
theorem meshExact_all_days_collapse {v : ℚ} {N : ℕ} (hN : 0 < N)
    (hmesh : ∀ n < N, ∃ k ≤ n + 1, v = (k : ℚ) / ((n : ℚ) + 1)) : v = 0 ∨ v = 1 := by
  obtain ⟨k, hk, hv⟩ := hmesh 0 hN
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · left; rw [hv]; norm_num
  · right; rw [hv]; norm_num

/-- Exactness at two consecutive days `n`, `n + 1` already forces `v ∈ {0, 1}`:
`v(n+1) = k`, `v(n+2) = k'` give `v = k' − k ∈ ℕ ∩ [0, 1]`. -/
theorem meshExact_consecutive_collapse {v : ℚ} (n : ℕ)
    (h0 : ∃ k ≤ n + 1, v = (k : ℚ) / ((n : ℚ) + 1))
    (h1 : ∃ k ≤ (n + 1) + 1, v = (k : ℚ) / (((n + 1 : ℕ) : ℚ) + 1)) : v = 0 ∨ v = 1 := by
  obtain ⟨k, hk, hv⟩ := h0
  obtain ⟨k', hk', hv'⟩ := h1
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hpos' : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) + 1 := by positivity
  have e1 : v * ((n : ℚ) + 1) = k := by rw [hv]; field_simp
  have e2 : v * (((n + 1 : ℕ) : ℚ) + 1) = k' := by rw [hv']; field_simp
  have hv_eq : v = (k' : ℚ) - k := by
    push_cast at e2
    linarith
  have h0v : 0 ≤ v := by rw [hv]; positivity
  have h1v : v ≤ 1 := by
    rw [hv, div_le_one hpos]; exact_mod_cast hk
  have hle : k ≤ k' := by
    have : (k : ℚ) ≤ k' := by linarith
    exact_mod_cast this
  have hle' : k' ≤ k + 1 := by
    have : (k' : ℚ) ≤ k + 1 := by linarith
    exact_mod_cast this
  have hcases : k' = k ∨ k' = k + 1 := by omega
  rcases hcases with rfl | rfl
  · left; rw [hv_eq]; ring
  · right; rw [hv_eq]; push_cast; ring

/-- The "lcm" claim is false: `v = ½` has denominator `2 ∣ lcm(1, 2) = 2`, yet it is not
mesh-exact on every day `< 2` (day `0`'s mesh is `{0, 1}`). -/
theorem half_not_meshExact_two :
    ¬ ∀ n : ℕ, n < 2 → ∃ k : ℕ, k ≤ n + 1 ∧ (1 / 2 : ℚ) = (k : ℚ) / ((n : ℚ) + 1) := by
  intro h
  obtain ⟨k, hk, hv⟩ := h 0 (by norm_num)
  have hk1 : k ≤ 1 := by simpa using hk
  interval_cases k <;> norm_num at hv

/-- At `v = ½`, `N = 2`, the steered advisor quotes `1` on day `0` — not `½`: the committed stream
does not carry `a_0(u) = v`. -/
theorem steeredAdvisor_half_day_zero (A : History) :
    quoteStreamR (steeredAdvisor A (1 / 2) 2) 0 = 1 := by
  rw [steeredAdvisor_quote A (1 / 2) (by norm_num : 0 < 2)]
  have h : ((Finset.range (0 + 1)).filter fun i : ℕ => (i : ℚ) / (((0 : ℕ) : ℚ) + 1) < 1 / 2)
      = {0} := by
    rw [zero_add, Finset.range_one, Finset.filter_singleton, if_pos (by norm_num)]
  rw [h, Finset.card_singleton]
  norm_num

/-- The ledger's and open list's "`v ∈ [0,1]` mesh-exact on every steering day", under `0 < N`,
is the two-element set: the hypothesis package of the `_steered` rows and of the OPEN is
satisfiable exactly at `v = 0` and `v = 1`. -/
theorem meshExact_all_days_iff {v : ℚ} {N : ℕ} (hN : 0 < N) :
    (∀ n < N, ∃ k ≤ n + 1, v = (k : ℚ) / ((n : ℚ) + 1)) ↔ (v = 0 ∨ v = 1) := by
  constructor
  · exact meshExact_all_days_collapse hN
  · rintro (rfl | rfl) <;> intro n _
    · exact ⟨0, by omega, by simp⟩
    · refine ⟨n + 1, le_rfl, ?_⟩
      have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
      push_cast
      rw [div_self hpos.ne']

end Cleanroom.Deference.DefDoseResponse.AuditR3
