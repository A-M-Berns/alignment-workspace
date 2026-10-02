import Cleanroom.Bli.BliRvcUi.Rvc.Defs
import Cleanroom.Bli.BliFound.Tags

/-!
# `bli-rvc-ui` · Rvc/Grid: real-value coherence (E) — exact fails at the mesh, ε holds (T1.1–T1.2)

**T1.1 (refuted).** Exact additivity of FAF's grid expectation `LUV.expectApprox` at finite
precision `k` fails **even at a single world that values `Z = X + Y`** — the failure is the grid,
not incoherence. The witness: three threshold families of fresh atoms (family `8`, day `0`, slots
`0`, `1`, `2`); the world holds `X.gt r ↔ r < 1/(2k)`, the same for `Y`, and `Z.gt r ↔ r < 1/k`.
It values `X` and `Y` at `1/(2k)` and `Z` at `1/k = 1/(2k) + 1/(2k)`; yet on the grid
`{i/k : i < k}` only `i = 0` pays for each of the three, so `𝔼ᵏ(X) = 𝔼ᵏ(Y) = 𝔼ᵏ(Z) = 1/k` and
`𝔼ᵏ(X) + 𝔼ᵏ(Y) = 2/k ≠ 1/k`. Do not read this as "coherent valuations are not additive": it is
"at precision `k` the mesh error is `≥ 1/k`" (mandate §5, mesh honesty).

**T1.2 (proved).** Over a finite mixture of worlds each valuing `Z = X + Y`, ε-additivity holds
with `ε = 3/k`, and each expectation is within `1/k` of the mixture's mean value — by
`PCWorld.ValuesAt.expectApprox_near` (`lem:conluvapprox`) and linearity of `expectApprox` in the
valuation. This is D-RVC(E_ε) as a theorem over finite propositional coherence; the process-relative
corollary (`Constraints.CoherentOn`) is `Rvc/Process.lean`.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Finset Cleanroom.Bli.BliFound

/-! ## Linearity of the grid expectation in the valuation -/

/-- The grid expectation of a finite mixture of valuations is the mixture of the grid
expectations, needing the mixture identity only on the grid thresholds `i/k`, `i < k`.
Source: FAF `LUV.expectApprox` (linear in `V`)
Kind: L
Fidelity: n/a -/
theorem expectApprox_mixture {ι : Type*} [Fintype ι] (V : Valuation) (W : ι → Valuation)
    (w : ι → ℝ) (k : ℕ) (X : LUV)
    (hV : ∀ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ))) =
      ∑ j, w j * W j (X.gt ((i : ℚ) / (k : ℚ)))) :
    X.expectApprox V k = ∑ j, w j * X.expectApprox (W j) k := by
  unfold LUV.expectApprox
  rw [Finset.mul_sum, Finset.sum_congr rfl fun i hi => by rw [hV i hi, Finset.mul_sum],
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **The grid expectation of a mixture of valued worlds is within `1/k` of the mixture's mean
value** (`lem:conluvapprox` mixed).
Source: FAF `PCWorld.ValuesAt.expectApprox_near`; mandate T1.2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expectApprox_mixture_near {ι : Type*} [Fintype ι] {V : Valuation} {W : ι → PCWorld}
    {w : ι → ℝ} {k : ℕ} (hk : 0 < k) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) {X : LUV}
    {x : ι → ℝ} (hval : ∀ j, (W j).ValuesAt X (x j))
    (hV : ∀ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ))) =
      ∑ j, w j * (W j).payout (X.gt ((i : ℚ) / (k : ℚ)))) :
    |X.expectApprox V k - ∑ j, w j * x j| ≤ 1 / k := by
  rw [expectApprox_mixture V (fun j => (W j).payout) w k X hV, ← Finset.sum_sub_distrib]
  calc |∑ j, (w j * X.expectApprox (W j).payout k - w j * x j)|
      ≤ ∑ j, |w j * X.expectApprox (W j).payout k - w j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, w j * |X.expectApprox (W j).payout k - x j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 j)]
    _ ≤ ∑ j, w j * (1 / k) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left ((hval j).expectApprox_near hk) (hw0 j)
    _ = 1 / k := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **T1.2 — ε-additivity of the grid expectation over a finite mixture of worlds valuing
`Z = X + Y`**, with `ε = 3/k` (three mesh errors), for every valuation agreeing with the mixture
on the grid thresholds of `X`, `Y` and `Z`.
Source: mandate T1.2; bli-slides-014 (E, the ε-form); [[bli-program-desiderata]] D-RVC(E_ε), I9
Kind: C
Fidelity: exact (the ε is the mesh, `3/k` at precision `k`)
Hyps: (a) -/
theorem rvcE_eps_of_worldMixture {ι : Type*} [Fintype ι] {V : Valuation} {W : ι → PCWorld}
    {w : ι → ℝ} {k : ℕ} (hk : 0 < k) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) {X Y Z : LUV}
    (hsum : ∀ j, SumValued (W j) X Y Z)
    (hX : ∀ i ∈ Finset.range k, V (X.gt ((i : ℚ) / (k : ℚ))) =
      ∑ j, w j * (W j).payout (X.gt ((i : ℚ) / (k : ℚ))))
    (hY : ∀ i ∈ Finset.range k, V (Y.gt ((i : ℚ) / (k : ℚ))) =
      ∑ j, w j * (W j).payout (Y.gt ((i : ℚ) / (k : ℚ))))
    (hZ : ∀ i ∈ Finset.range k, V (Z.gt ((i : ℚ) / (k : ℚ))) =
      ∑ j, w j * (W j).payout (Z.gt ((i : ℚ) / (k : ℚ)))) :
    RVC_E_eps V k X Y Z (3 / k) := by
  choose x y hx hy hz using hsum
  have hXn := expectApprox_mixture_near hk hw0 hw1 hx hX
  have hYn := expectApprox_mixture_near hk hw0 hw1 hy hY
  have hZn := expectApprox_mixture_near hk hw0 hw1 hz hZ
  have hsplit : ∑ j, w j * (x j + y j) = ∑ j, w j * x j + ∑ j, w j * y j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit] at hZn
  unfold RVC_E_eps
  have h3 : (3 : ℝ) / k = 1 / k + 1 / k + 1 / k := by ring
  rw [h3]
  calc |X.expectApprox V k + Y.expectApprox V k - Z.expectApprox V k|
      = |(X.expectApprox V k - ∑ j, w j * x j) + (Y.expectApprox V k - ∑ j, w j * y j)
          - (Z.expectApprox V k - (∑ j, w j * x j + ∑ j, w j * y j))| := by ring_nf
    _ ≤ |X.expectApprox V k - ∑ j, w j * x j| + |Y.expectApprox V k - ∑ j, w j * y j|
          + |Z.expectApprox V k - (∑ j, w j * x j + ∑ j, w j * y j)| := by
        calc _ ≤ |(X.expectApprox V k - ∑ j, w j * x j) + (Y.expectApprox V k - ∑ j, w j * y j)|
              + |Z.expectApprox V k - (∑ j, w j * x j + ∑ j, w j * y j)| := abs_sub _ _
          _ ≤ _ := by
              gcongr
              exact abs_add_le _ _
    _ ≤ 1 / k + 1 / k + 1 / k := by gcongr

/-- **T1.2 at the mixture itself**: for `V = ∑ j, w j • (W j).payout` (as a valuation), the
`3/k` bound.
Source: mandate T1.2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem rvcE_eps_of_worldMarginal {ι : Type*} [Fintype ι] {W : ι → PCWorld} {w : ι → ℝ} {k : ℕ}
    (hk : 0 < k) (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) {X Y Z : LUV}
    (hsum : ∀ j, SumValued (W j) X Y Z) :
    RVC_E_eps (fun φ => ∑ j, w j * (W j).payout φ) k X Y Z (3 / k) :=
  rvcE_eps_of_worldMixture hk hw0 hw1 hsum (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-! ## T1.1 — exact additivity fails at the mesh, at a single world -/

/-- The three threshold families of the T1.1 witness: fresh atoms of family `8`, day `0`, slot `j`.
Source: mandate T1.1 (registry: family `8`, payload `⟨0, ⟨j, encode r⟩⟩`)
Kind: D
Fidelity: n/a -/
def gridLuv (j : ℕ) : LUV where
  gt r := freshAtom 8 (Nat.pair 0 (Nat.pair j (Encodable.encode r)))

/-- The value the T1.1 world assigns to slot `j`: `1/k` for `Z` (`j = 2`), `1/(2k)` for `X`, `Y`.
Source: mandate T1.1
Kind: D
Fidelity: n/a -/
noncomputable def gridValue (k j : ℕ) : ℝ := if j = 2 then 1 / k else 1 / (2 * k)

/-- The T1.1 world: holds `(gridLuv j).gt r` iff `r < gridValue k j`; every other atom false.
Source: mandate T1.1
Kind: D
Fidelity: n/a -/
def gridWorld (k : ℕ) : PCWorld := fun a =>
  ∃ (j : ℕ) (r : ℚ), a = freshAtomCode 8 (Nat.pair 0 (Nat.pair j (Encodable.encode r))) ∧
    (r : ℝ) < gridValue k j

/-- `holds_gridWorld_gt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_gridWorld_gt (k j : ℕ) (r : ℚ) :
    (gridWorld k).Holds ((gridLuv j).gt r) ↔ (r : ℝ) < gridValue k j := by
  show gridWorld k (freshAtomCode 8 (Nat.pair 0 (Nat.pair j (Encodable.encode r)))) ↔ _
  constructor
  · rintro ⟨j', r', h, hlt⟩
    have h' := (freshAtomCode_inj.mp h).2
    rw [Nat.pair_eq_pair, Nat.pair_eq_pair] at h'
    obtain ⟨-, hj, hr⟩ := h'
    rw [hj, Encodable.encode_inj.mp hr]
    exact hlt
  · intro hlt
    exact ⟨j, r, rfl, hlt⟩

/-- The T1.1 world values slot `j` at `gridValue k j` (for `1 ≤ k`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridWorld_valuesAt {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (gridWorld k).ValuesAt (gridLuv j) (gridValue k j) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  refine ⟨?_, ?_, fun r => ⟨fun h => (holds_gridWorld_gt k j r).mpr h,
    fun h hh => absurd ((holds_gridWorld_gt k j r).mp hh) (not_lt.mpr h.le)⟩⟩
  · unfold gridValue
    split_ifs <;> positivity
  · unfold gridValue
    split_ifs
    · rw [div_le_one hkpos]; exact hk'
    · rw [div_le_one (by linarith)]; linarith

/-- The T1.1 world values `Z` as `X + Y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridWorld_sumValued {k : ℕ} (hk : 1 ≤ k) :
    SumValued (gridWorld k) (gridLuv 0) (gridLuv 1) (gridLuv 2) := by
  refine ⟨gridValue k 0, gridValue k 1, gridWorld_valuesAt hk 0, gridWorld_valuesAt hk 1, ?_⟩
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have h : gridValue k 0 + gridValue k 1 = gridValue k 2 := by
    unfold gridValue
    rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
    field_simp
    ring
  rw [h]
  exact gridWorld_valuesAt hk 2

/-- On the grid `{i/k : i < k}` only `i = 0` pays, for each of the three slots, so each grid
expectation is exactly `1/k`.
Source: mandate T1.1 (the computation)
Kind: L
Fidelity: n/a -/
lemma gridWorld_expectApprox {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (gridLuv j).expectApprox (gridWorld k).payout k = 1 / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  unfold LUV.expectApprox
  have hpay : ∀ i : ℕ, (gridWorld k).payout ((gridLuv j).gt ((i : ℚ) / (k : ℚ))) =
      if i = 0 then 1 else 0 := by
    intro i
    unfold PCWorld.payout
    rw [holds_gridWorld_gt]
    have hcast : (((i : ℚ) / (k : ℚ) : ℚ) : ℝ) = (i : ℝ) / k := by push_cast; ring
    rw [hcast]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, if_pos]
      simp only [Nat.cast_zero, zero_div]
      unfold gridValue
      split_ifs <;> positivity
    · rw [if_neg hi, if_neg]
      have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
      unfold gridValue
      have h1 : (1 : ℝ) / k ≤ (i : ℝ) / k := by gcongr
      have h2 : (1 : ℝ) / (2 * k) ≤ (1 : ℝ) / k :=
        one_div_le_one_div_of_le hkpos (by linarith)
      split_ifs <;> linarith
  simp_rw [hpay]
  rw [Finset.sum_ite_eq' (Finset.range k) 0 (fun _ => (1 : ℝ)), if_pos (Finset.mem_range.mpr hk)]
  ring

/-- **T1.1 — exact additivity of FAF's grid expectation at finite precision fails even for a world
that values `Z = X + Y`** (refuted; N+). For every `k ≥ 1` there are a world and three LUVs with
`SumValued` and `𝔼ᵏ(X) + 𝔼ᵏ(Y) = 2/k ≠ 1/k = 𝔼ᵏ(Z)`. The world is a *single* world — maximally
coherent — so the failure is the grid, not incoherence: exact (E) is a mesh artifact, and the
satisfiable finite-day form is `RVC_E_eps` (T1.2).
Source: `main.tex:349`; bli-slides-014 (E) and its annotation; [[bli-program-desiderata]] I9
Kind: N+
Fidelity: exact (refutes exact (E) at every finite precision)
Hyps: (a) -/
theorem rvcE_exact_fails : ∀ k ≥ 1, ∃ (v : PCWorld) (X Y Z : LUV),
    SumValued v X Y Z ∧ ¬ RVC_E_exact v.payout k X Y Z := by
  intro k hk
  refine ⟨gridWorld k, gridLuv 0, gridLuv 1, gridLuv 2, gridWorld_sumValued hk, ?_⟩
  unfold RVC_E_exact
  rw [gridWorld_expectApprox hk 0, gridWorld_expectApprox hk 1, gridWorld_expectApprox hk 2]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  intro h
  have : (1 : ℝ) / k = 0 := by linarith
  exact absurd this (by positivity)

end Cleanroom.Bli.BliRvcUi
