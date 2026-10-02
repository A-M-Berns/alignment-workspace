import Cleanroom.Lit.LitShutdownPrefs.TimestepDominance

/-!
# POST as unanimity aggregation (Target 14; positive/thornley.md A2)

For a trajectory utility `u`, the value-of-lifetime family is `V k t = u t + k · len t`,
`k ∈ ℝ`, aggregated by *unanimity*: `t ≽ t' iff V k t ≥ V k t' for all k`. Then same-length
trajectories are ranked by `u`, and different-length trajectories are incomparable (`k` can be
chosen with either sign) — that is POST exactly (`post_unanimity`), with a non-triviality witness
(`unanimity_nontrivial`).

Lottery extension (`leUL`): `X ≽ Y iff E_X[len] = E_Y[len] ∧ E_X[u] ≥ E_Y[u]` (`leUL_iff`).
Negative halves: Allow/Resist (2025 §8) have `E[len] = 1.1 ≠ 1.9`, so they are incomparable —
**unanimity satisfies POST but not Neutrality** (`not_neutrality_unanimity`); and unanimity also
**violates POSL** (`not_posl_unanimity`): `dirac [0,0]` and `½[1] + ½[0,0,0]` have equal mean
length and different length supports, and `u = sumTotal` ranks them.
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace Unanimity

open Lottery Strict

/-- The value-of-lifetime hypothesis `V k t = u t + k · len t`.
Source: positive/thornley.md A2 (`V_k(t) := u(t) + k · len(t)`); corr-wf13-081
Kind: D
Fidelity: exact -/
def V (u : Traj → ℝ) (k : ℝ) (t : Traj) : ℝ := u t + k * (len t : ℝ)

/-- Unanimity weak preference on lotteries: `X ≽ Y` iff `E_X[V k] ≥ E_Y[V k]` for every `k`.
Source: positive/thornley.md A2 ("aggregate by unanimity")
Kind: D
Fidelity: exact -/
def leUL (u : Traj → ℝ) (X Y : Lottery Traj) : Prop := ∀ k : ℝ, Y.expect (V u k) ≤ X.expect (V u k)

/-- Unanimity strict preference on lotteries.
Source: positive/thornley.md A2
Kind: D
Fidelity: exact -/
def ltUL (u : Traj → ℝ) (X Y : Lottery Traj) : Prop := leUL u X Y ∧ ¬ leUL u Y X

/-- The mean length of a lottery.
Source: none: infrastructure
Kind: D -/
noncomputable def meanLen (X : Lottery Traj) : ℝ := X.expect (fun t => (len t : ℝ))

/-- `E_X[V k] = E_X[u] + k · E_X[len]`.
Source: none: infrastructure
Kind: L -/
theorem expect_V (u : Traj → ℝ) (k : ℝ) (X : Lottery Traj) :
    X.expect (V u k) = X.expect u + k * meanLen X := by
  unfold V meanLen
  rw [← expect_smul, ← expect_add]

/-- **Lottery extension of unanimity**: `X ≽ Y iff E_X[len] = E_Y[len] ∧ E_Y[u] ≤ E_X[u]`.
Source: positive/thornley.md A2 (negative half, `[checked]`); [[lit-shutdown-prefs-mandate]] Target 14
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem leUL_iff (u : Traj → ℝ) (X Y : Lottery Traj) :
    leUL u X Y ↔ meanLen X = meanLen Y ∧ Y.expect u ≤ X.expect u := by
  unfold leUL
  simp only [expect_V]
  constructor
  · intro h
    have h0 := h 0
    simp only [zero_mul, add_zero] at h0
    refine ⟨?_, h0⟩
    by_contra hne
    have hd : meanLen Y - meanLen X ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hk := h ((X.expect u - Y.expect u + 1) / (meanLen Y - meanLen X))
    have : (X.expect u - Y.expect u + 1) / (meanLen Y - meanLen X) * (meanLen Y - meanLen X) =
        X.expect u - Y.expect u + 1 := div_mul_cancel₀ _ hd
    nlinarith
  · rintro ⟨h1, h2⟩ k
    rw [h1]
    linarith

/-- On point masses, `meanLen (dirac t) = len t`.
Source: none: infrastructure
Kind: L -/
@[simp] theorem meanLen_dirac (t : Traj) : meanLen (dirac t) = len t := by simp [meanLen]

/-- **Same-length trajectories are ranked by `u`** under unanimity.
Source: positive/thornley.md A2; [[lit-shutdown-prefs-mandate]] Target 14
Kind: P
Fidelity: exact -/
theorem ltUL_dirac_iff_of_len_eq (u : Traj → ℝ) {t t' : Traj} (h : len t = len t') :
    ltUL u (dirac t) (dirac t') ↔ u t' < u t := by
  unfold ltUL
  rw [leUL_iff, leUL_iff]
  simp [h]
  exact fun h => le_of_lt h

/-- **Different-length trajectories are incomparable** under unanimity.
Source: positive/thornley.md A2; [[lit-shutdown-prefs-mandate]] Target 14
Kind: P
Fidelity: exact -/
theorem lacks_dirac_of_len_ne (u : Traj → ℝ) {t t' : Traj} (h : len t ≠ len t') :
    lacks (ltUL u) (dirac t) (dirac t') := by
  constructor
  · rintro ⟨hle, -⟩
    rw [leUL_iff] at hle
    simp at hle
    exact h hle.1
  · rintro ⟨hle, -⟩
    rw [leUL_iff] at hle
    simp at hle
    exact h hle.1.symm

/-- **POST holds for unanimity aggregation**, for every `u`.
Source: positive/thornley.md A2 (`[checked]`); corr-wf13-081; [[lit-shutdown-prefs-mandate]] Target 14
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem post_unanimity (u : Traj → ℝ) : POST (ltUL u) :=
  fun _ _ h => lacks_dirac_of_len_ne u h

/-- With `u = sumTotal` the unanimity agent's same-length preferences are non-trivial
(`[1] ≻ [0]`): the non-triviality witness for `post_unanimity` (split off at audit round 1,
fidelity non-blocking 8).
Source: positive/thornley.md A2; [[lit-shutdown-prefs-mandate]] Target 14
Kind: N+
Fidelity: n/a -/
theorem unanimity_nontrivial : ltUL sumTotal (dirac [1]) (dirac [0]) := by
  rw [ltUL_dirac_iff_of_len_eq sumTotal (by simp [len])]
  simp [sumTotal]

/-- Conditioning on two events that agree on the support gives the same sublottery.
Source: none: infrastructure
Kind: L -/
theorem condOn_congr (X : Lottery Traj) (q q' : Traj → Prop) [DecidablePred q] [DecidablePred q']
    (h : 0 < X.mass q) (h' : 0 < X.mass q') (hq : ∀ t ∈ X.support, (q t ↔ q' t)) :
    X.condOn q h = X.condOn q' h' := by
  have hm : X.mass q = X.mass q' := by
    unfold mass; apply X.expect_congr; intro t ht; simp [hq t ht]
  ext1
  show (X.mass q)⁻¹ • X.p.filter q = (X.mass q')⁻¹ • X.p.filter q'
  rw [hm]
  congr 1
  ext t
  simp only [Finsupp.filter_apply]
  by_cases ht : t ∈ X.support
  · simp [hq t ht]
  · have : X.p t = 0 := Finsupp.notMem_support_iff.mp ht
    simp [this]

/-- The support of a two-point lottery is contained in its two points.
Source: none: infrastructure
Kind: L -/
theorem support_mix_dirac_subset (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (t t' : Traj) :
    (mix a ha (dirac t) (dirac t')).support ⊆ {t, t'} := by
  intro s hs
  have := (mem_support_iff_pos _ s).mp hs
  simp only [mix_p, dirac, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at this
  by_contra hc
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  rw [Finsupp.single_eq_of_ne hc.1, Finsupp.single_eq_of_ne hc.2] at this
  simp at this

/-- The length-`len t` conditional of `a·[t] + (1−a)·[t']` (different lengths) is `dirac t`.
Source: none: infrastructure
Kind: L -/
theorem condLen_mix_dirac_left (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (h0 : 0 < a) (h1 : a < 1)
    (t t' : Traj) (hne : len t ≠ len t') (hl : len t ∈ (mix a ha (dirac t) (dirac t')).lengths) :
    (mix a ha (dirac t) (dirac t')).condLen (len t) hl = dirac t := by
  unfold condLen
  have hpt : 0 < (mix a ha (dirac t) (dirac t')).mass (fun s => s = t) := by
    rw [mass_eq_point]
    have htt' : t ≠ t' := fun e => hne (by rw [e])
    simp [mix_p, dirac, Finsupp.single_eq_of_ne htt', h0]
  rw [condOn_congr _ _ (fun s => s = t) _ hpt, condOn_point]
  intro s hs
  have hs' := support_mix_dirac_subset a ha t t' hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
  rcases hs' with rfl | rfl
  · simp
  · simp [hne.symm]
    intro h; exact hne (by rw [h])

/-- The length-`len t'` conditional of `a·[t] + (1−a)·[t']` (different lengths) is `dirac t'`.
Source: none: infrastructure
Kind: L -/
theorem condLen_mix_dirac_right (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (h0 : 0 < a) (h1 : a < 1)
    (t t' : Traj) (hne : len t ≠ len t') (hl : len t' ∈ (mix a ha (dirac t) (dirac t')).lengths) :
    (mix a ha (dirac t) (dirac t')).condLen (len t') hl = dirac t' := by
  unfold condLen
  have hpt : 0 < (mix a ha (dirac t) (dirac t')).mass (fun s => s = t') := by
    rw [mass_eq_point]
    have : t ≠ t' := fun h => hne (by rw [h])
    simp [mix_p, dirac, Finsupp.single_eq_of_ne (Ne.symm this)]
    linarith
  rw [condOn_congr _ _ (fun s => s = t') _ hpt, condOn_point]
  intro s hs
  have hs' := support_mix_dirac_subset a ha t t' hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
  rcases hs' with rfl | rfl
  · simp [hne]
    intro h; exact hne (by rw [h])
  · simp

/-- **Unanimity satisfies POST but not Neutrality**: on Thornley 2025 §8's Allow/Resist pair (=
`leave`/`block`) all three antecedents of Neutrality hold for `u = sumTotal`, yet the two lotteries
are incomparable because `E[len] = 1.1 ≠ 1.9`. ILPACS is the extra ingredient.
Source: positive/thornley.md A2 (negative half, `[checked]`); [[lit-shutdown-prefs-mandate]] Target 14
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem not_neutrality_unanimity :
    NeutralityAntecedents (ltUL sumTotal) leave block ∧ lacks (ltUL sumTotal) leave block ∧
      ¬ Neutrality (ltUL sumTotal) := by
  have hL : leave.lengths = {1, 2} := by
    unfold leave; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  have hB : block.lengths = {1, 2} := by
    unfold block; rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  have hS : SameLength leave block := by unfold SameLength; rw [hL, hB]
  have hlacks : lacks (ltUL sumTotal) leave block := by
    have hmL : meanLen leave = 11/10 := by simp [meanLen, leave, len]; norm_num
    have hmB : meanLen block = 19/10 := by simp [meanLen, block, len]; norm_num
    constructor
    · rintro ⟨h, -⟩; rw [leUL_iff, hmL, hmB] at h; norm_num at h
    · rintro ⟨h, -⟩; rw [leUL_iff, hmL, hmB] at h; norm_num at h
  have hc1 : ∀ hl, leave.condLen 1 hl = dirac [1] :=
    fun hl => condLen_mix_dirac_left (9/10) (by norm_num) (by norm_num) (by norm_num) [1] [1, 2]
      (by simp [len]) hl
  have hc2 : ∀ hl, leave.condLen 2 hl = dirac [1, 2] :=
    fun hl => condLen_mix_dirac_right (9/10) (by norm_num) (by norm_num) (by norm_num) [1] [1, 2]
      (by simp [len]) hl
  have hd1 : ∀ hl, block.condLen 1 hl = dirac [0] :=
    fun hl => condLen_mix_dirac_left (1/10) (by norm_num) (by norm_num) (by norm_num) [0] [0, 2]
      (by simp [len]) hl
  have hd2 : ∀ hl, block.condLen 2 hl = dirac [0, 2] :=
    fun hl => condLen_mix_dirac_right (1/10) (by norm_num) (by norm_num) (by norm_num) [0] [0, 2]
      (by simp [len]) hl
  have hant : NeutralityAntecedents (ltUL sumTotal) leave block := by
    refine ⟨hS, fun l hl => ?_, ⟨1, by rw [hL]; simp, ?_⟩⟩
    · have hl' := hl
      rw [hL] at hl'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
      rcases hl' with rfl | rfl
      · rw [hc1, hd1]
        exact Or.inl ((ltUL_dirac_iff_of_len_eq _ (by simp [len])).mpr (by simp [sumTotal]))
      · rw [hc2, hd2]
        exact Or.inl ((ltUL_dirac_iff_of_len_eq _ (by simp [len])).mpr (by simp [sumTotal]))
    · rw [hc1, hd1]
      exact (ltUL_dirac_iff_of_len_eq _ (by simp [len])).mpr (by simp [sumTotal])
  exact ⟨hant, hlacks, fun hN => hlacks.1 (hN _ _ hant)⟩

/-- **Unanimity violates POSL**: `X = dirac [0,0]` and `Y = ½[1] + ½[0,0,0]` have equal mean
length `2` and different length sets, and with `u = sumTotal`, `Y ≻ X`.
Source: [[lit-shutdown-prefs-mandate]] Target 14 (mandate-writer claim, verified)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem not_posl_unanimity : ¬ POSL (ltUL sumTotal) := by
  intro hP
  have h := hP (mix (1/2) (by norm_num) (dirac [1]) (dirac [0, 0, 0])) (dirac [0, 0]) ?_
  · unfold SameLength at h
    rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)] at h
    have : (2 : ℕ) ∈ (dirac ([0, 0] : Traj)).lengths := by
      rw [mem_lengths_iff]; simp [mass, len]
    rw [← h] at this
    simp [len] at this
  · unfold ltUL
    rw [leUL_iff, leUL_iff]
    simp [meanLen, len, sumTotal]
    norm_num

end Unanimity

end Cleanroom.Lit.LitShutdownPrefs
