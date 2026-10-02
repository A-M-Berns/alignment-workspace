import Cleanroom.Bli.BliFinite.WorldRound
import Cleanroom.Bli.BliFinite.CoherenceExamples
import Cleanroom.Bli.BliFinite.Superbelief

/-!
# `bli-finite` · FaceCoherent: on the coherent grid the face is not a product (extension)

`S = {p, q, p ⋏ q}`, `d = 2`, `t = (1/2, 1/2, 0)`. The zero table `Q₀ = (0, 0, 0)` lies on the
coherent grid (all world mass on `¬p ∧ ¬q`) and in the product face over `t` (it agrees with
`t` at the one pinned coordinate `p ⋏ q`), but **no** balance solution on the coherent grid
charges it: coherent tables with `Q (p ⋏ q) = 0` satisfy `Q p + Q q ≤ 1`, the mean has
`t p + t q = 1`, so the support lies on `{Q p + Q q = 1}`, which excludes `Q₀`. Hence
`faceGen (coherentGrid …) t ⊊ faceProd t ∩ coherentGrid`: the coherent-grid face theorem
(`bli-superbelief` E1, `bli-coherent-mm`) must handle a face that is not a product.
-/

namespace Cleanroom.Bli.BliFinite

open LogicalInduction LO.Propositional Finset BoolPCWorld Classical

/-- The extension's index: `S m = {p, q, p ⋏ q}` on every day.
Source: mandate extension
Kind: D
Fidelity: n/a -/
def extIndex : SmallIndex := ⟨fun _ => {pA, qA, pA ⋏ qA}, fun _ => Finset.Subset.refl _⟩

/-- The extension's mesh: `d = 2` on every day.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def extMesh : Mesh := ⟨fun _ => 2, fun _ => by norm_num, fun _ => dvd_refl 2⟩

/-- `p` is small on every day of the extension index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pA_mem_ext (m : ℕ) : pA ∈ extIndex.S m := by simp [extIndex]
/-- `q` is small on every day of the extension index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma qA_mem_ext (m : ℕ) : qA ∈ extIndex.S m := by simp [extIndex]
/-- `p ⋏ q` is small on every day of the extension index.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pq_mem_ext (m : ℕ) : pA ⋏ qA ∈ extIndex.S m := by simp [extIndex]

/-- The day-0 table `(1/2, 1/2, 0)`.
Source: mandate extension
Kind: D
Fidelity: n/a -/
def extT : Table extIndex 0 := fun φ => if φ.1 = pA ⋏ qA then 0 else 1 / 2

/-- The zero day-1 table.
Source: mandate extension
Kind: D
Fidelity: n/a -/
def extQ₀ : Table extIndex 1 := fun _ => 0

/-- The world `¬p ∧ ¬q`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wnPnQ : FiniteWorld 2 := ![false, false]

/-- The world `¬p ∧ ¬q` pays `0` on every extension sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_wnPnQ (φ : Sentence) (hφ : φ ∈ extIndex.S 1) : wnPnQ.payoutRat φ = 0 := by
  simp only [extIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
  rcases hφ with rfl | rfl | rfl <;> decide

/-- Two units of world mass on `¬p ∧ ¬q`, none elsewhere.
Source: mandate extension
Kind: D
Fidelity: n/a -/
def extC (u : FiniteWorld 2) : Fin (extMesh.d 1 + 1) :=
  if u = wnPnQ then ⟨2, by norm_num [extMesh]⟩ else ⟨0, by norm_num⟩

/-- The integer weights: `2` at `¬p ∧ ¬q`, `0` elsewhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma extC_val (u : FiniteWorld 2) : (extC u).val = if u = wnPnQ then 2 else 0 := by
  unfold extC; split_ifs <;> rfl

/-- **`Q₀` is on the coherent grid** (all two units of world mass on `¬p ∧ ¬q`).
Source: mandate extension
Kind: L
Fidelity: n/a -/
lemma extQ₀_mem_coherentGrid : extQ₀ ∈ coherentGrid extIndex extMesh.d 1 ∅ 2 := by
  unfold coherentGrid
  rw [Finset.mem_image]
  refine ⟨extC, ?_, ?_⟩
  · unfold worldWeights
    rw [Finset.mem_filter]
    refine ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, ?_, ?_⟩
    · simp only [extC_val, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    · intro u _ φ hφ; simp at hφ
  · funext φ
    unfold marginalOf extQ₀
    have hval : ∀ u : FiniteWorld 2, (((extC u).val : ℕ) : ℚ) / (extMesh.d 1 : ℚ) =
        if u = wnPnQ then 1 else 0 := by
      intro u
      rw [extC_val]
      show _ / ((2 : ℕ) : ℚ) = _
      split_ifs <;> norm_num
    simp only [hval, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact payout_wnPnQ φ.1 φ.2

/-- **`Q₀` is in the product face over `t`** (the only pinned coordinate is `p ⋏ q`, at 0).
Source: mandate extension
Kind: L
Fidelity: n/a -/
lemma extQ₀_mem_faceProd : extQ₀ ∈ faceProd extIndex extMesh.d 0 extT := by
  rw [mem_faceProd_iff]
  refine ⟨mem_grid_iff.mpr fun _ => zero_mem_gridVals _, fun φ hφ => ?_⟩
  unfold extQ₀ extT at *
  rw [Table.restrict_apply]
  rcases hφ with h | h
  · exact h.symm
  · exfalso; split_ifs at h <;> norm_num at h

/-- For every world, `[p] + [q] ≤ 1 + [p ⋏ q]`.
Source: none: infrastructure (Boolean)
Kind: L
Fidelity: n/a -/
lemma payoutRat_p_add_q_le {B : ℕ} (u : FiniteWorld B) :
    u.payoutRat pA + u.payoutRat qA ≤ 1 + u.payoutRat (pA ⋏ qA) := by
  rw [payoutRat_eq_ite, payoutRat_eq_ite, payoutRat_eq_ite, PCWorld.holds_and]
  by_cases hp : (worldOf u).Holds pA <;> by_cases hq : (worldOf u).Holds qA <;> simp [hp, hq]

/-- On the coherent grid, `Q p + Q q ≤ 1 + Q (p ⋏ q)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coherentGrid_p_add_q_le {Q : Table extIndex 1} (hQ : Q ∈ coherentGrid extIndex extMesh.d 1 ∅ 2) :
    Q ⟨pA, pA_mem_ext 1⟩ + Q ⟨qA, qA_mem_ext 1⟩ ≤ 1 + Q ⟨pA ⋏ qA, pq_mem_ext 1⟩ := by
  obtain ⟨w, hw0, hw1, -, ht⟩ := coherentOn_of_mem_coherentGrid (extMesh.d_pos 1) hQ
  rw [ht, ht, ht, ← hw1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  have := payoutRat_p_add_q_le u
  nlinarith [hw0 u]

/-- **On the coherent grid the face is not a product**: `Q₀` lies in `faceProd t ∩ coherentGrid`
but carries no mass in any balance solution supported on the coherent grid.
Source: mandate extension; [[bli-program]] §3.4 ("on the coherent grid the face is not a
product")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem faceGen_coherentGrid_not_prod :
    extQ₀ ∈ faceProd extIndex extMesh.d 0 extT ∧
    extQ₀ ∈ coherentGrid extIndex extMesh.d 1 ∅ 2 ∧
    extQ₀ ∉ faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT := by
  refine ⟨extQ₀_mem_faceProd, extQ₀_mem_coherentGrid, ?_⟩
  intro h
  obtain ⟨-, F, hF, hmean, hpos⟩ := mem_faceGen_iff.mp h
  set G := coherentGrid extIndex extMesh.d 1 ∅ 2 with hG
  have hp : meanOn G F ⟨pA, pA_mem_ext 1⟩ = 1 / 2 := by
    have := congrFun hmean ⟨pA, pA_mem_ext 0⟩
    rw [Table.restrict_apply] at this
    rw [this]; unfold extT; rw [if_neg (fun h => by cases h)]
  have hq : meanOn G F ⟨qA, qA_mem_ext 1⟩ = 1 / 2 := by
    have := congrFun hmean ⟨qA, qA_mem_ext 0⟩
    rw [Table.restrict_apply] at this
    rw [this]; unfold extT; rw [if_neg (fun h => by cases h)]
  have hpq : meanOn G F ⟨pA ⋏ qA, pq_mem_ext 1⟩ = 0 := by
    have := congrFun hmean ⟨pA ⋏ qA, pq_mem_ext 0⟩
    rw [Table.restrict_apply] at this
    rw [this]; unfold extT; rw [if_pos rfl]
  -- termwise `F Q (Q p + Q q) ≤ F Q (1 + Q (p ⋏ q))`, with equal sums
  have hle : ∀ Q ∈ G, F Q * (Q ⟨pA, pA_mem_ext 1⟩ + Q ⟨qA, qA_mem_ext 1⟩) ≤
      F Q * (1 + Q ⟨pA ⋏ qA, pq_mem_ext 1⟩) :=
    fun Q hQ => mul_le_mul_of_nonneg_left (coherentGrid_p_add_q_le hQ) (hF.1 Q)
  have hsum : ∑ Q ∈ G, F Q * (Q ⟨pA, pA_mem_ext 1⟩ + Q ⟨qA, qA_mem_ext 1⟩) =
      ∑ Q ∈ G, F Q * (1 + Q ⟨pA ⋏ qA, pq_mem_ext 1⟩) := by
    simp only [mul_add, Finset.sum_add_distrib, mul_one]
    change meanOn G F _ + meanOn G F _ = _ + meanOn G F _
    rw [hp, hq, hpq, hF.2.2]; norm_num
  have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum extQ₀ (hF.mem_of_pos hpos)
  unfold extQ₀ at this
  simp only [add_zero, mul_zero, mul_one] at this
  exact hpos.ne this

end Cleanroom.Bli.BliFinite
