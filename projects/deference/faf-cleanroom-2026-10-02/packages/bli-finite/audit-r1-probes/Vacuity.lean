import Cleanroom.Bli.BliFinite.Witness
import Cleanroom.Bli.BliFinite.FaceCoherent
import Cleanroom.Bli.BliFinite.DeFinetti

/-!
# `bli-finite` · audit round 1 (adversarial) · probes

Evidence file for `bli-finite-audit-r1-adversarial.md`. **Not imported by the library.**
Each probe is a claim the audit checked by elaboration; a probe that elaborates is evidence,
a probe that fails to elaborate would have been reported as such.

* P1 — the tie rule of `roundVal` is "down", as its docstring says.
* P2 — the coherent-grid face over `extT` is nonempty (so `faceGen_coherentGrid_not_prod`
  exhibits a *proper* defect of a nonempty face, not an empty one).
* P3 — the `D`-relativized coherence is inhabited with `D ≠ ∅`, and `D` bites: the same table
  is coherent at `D = ∅` and not at `D = {p}`.
* P4 — `hB` is load-bearing in `twoAxiom_iff_worldMarginal`: without it the iff is false
  (the `toBoolPCWorld` `false`-default decides an atom of `D` beyond `B`).
* P5 — `Balanced` is a real constraint: the point mass at a grid table is `IsProb` and not
  balanced at `t₀`.
* P6 — `t.InUnit` is load-bearing in `faceProd_eq_faceGen`: off the cube `faceGen = ∅` while
  `faceProd` is the whole grid.
* P7 — the degenerate index with `S m = ∅` everywhere makes `Balanced` vacuous (recorded; the
  T9 witness has `|S 1| = 2`).
-/

namespace Cleanroom.Bli.BliFinite.AuditR1

open LogicalInduction LO.Propositional Finset BoolPCWorld Classical
open Cleanroom.Bli.BliFinite

/-! ## P1 — ties round down -/

/-- `1/4` at `d = 2` is halfway between `0` and `1/2`; it rounds to `0`. -/
example : roundVal 2 (1 / 4) = 0 := by
  have h : ⌈clamp01 (1 / 4 : ℚ) * (2 : ℕ) - 1 / 2⌉ = 0 := by
    rw [clamp01_eq_self (by norm_num), Int.ceil_eq_iff]; push_cast; constructor <;> norm_num
  unfold roundVal; rw [h]; norm_num

/-- `3/4` at `d = 2` is halfway between `1/2` and `1`; it rounds to `1/2`. -/
example : roundVal 2 (3 / 4) = 1 / 2 := by
  have h : ⌈clamp01 (3 / 4 : ℚ) * (2 : ℕ) - 1 / 2⌉ = 1 := by
    rw [clamp01_eq_self (by norm_num), Int.ceil_eq_iff]; push_cast; constructor <;> norm_num
  unfold roundVal; rw [h]; norm_num

/-! ## Helpers -/

/-- Truth in `worldOf u` from a payout of `1`. -/
lemma holds_of_payoutRat_eq_one {B : ℕ} {u : FiniteWorld B} {φ : Sentence}
    (h : u.payoutRat φ = 1) : (worldOf u).Holds φ := by
  rw [payoutRat_eq_ite] at h
  split_ifs at h with hh
  · exact hh
  · norm_num at h

/-! ## P2 — the coherent-grid face over `extT` is nonempty -/

/-- The day-1 copy of `extT = (1/2, 1/2, 0)`. -/
def extT1 : Table extIndex 1 := fun φ => if φ.1 = pA ⋏ qA then 0 else 1 / 2

/-- One unit of world mass on `p ∧ ¬q`, one on `¬p ∧ q`. -/
def extC' (u : FiniteWorld 2) : Fin (extMesh.d 1 + 1) :=
  if u = wPnQ then ⟨1, by norm_num [extMesh]⟩
  else if u = wnPQ then ⟨1, by norm_num [extMesh]⟩ else ⟨0, by norm_num⟩

lemma extC'_val (u : FiniteWorld 2) :
    (extC' u).val = (if u = wPnQ then 1 else 0) + (if u = wnPQ then 1 else 0) := by
  unfold extC'
  by_cases h1 : u = wPnQ
  · subst h1; simp [wPnQ_ne_wnPQ]
  · by_cases h2 : u = wnPQ
    · subst h2; simp [Ne.symm wPnQ_ne_wnPQ]
    · simp [h1, h2]

lemma payout_wPnQ_p : wPnQ.payoutRat pA = 1 := by decide
lemma payout_wPnQ_q : wPnQ.payoutRat qA = 0 := by decide
lemma payout_wPnQ_pq : wPnQ.payoutRat (pA ⋏ qA) = 0 := by decide
lemma payout_wnPQ_p : wnPQ.payoutRat pA = 0 := by decide
lemma payout_wnPQ_q : wnPQ.payoutRat qA = 1 := by decide
lemma payout_wnPQ_pq : wnPQ.payoutRat (pA ⋏ qA) = 0 := by decide

/-- `extT1` is on the coherent grid. -/
lemma extT1_mem_coherentGrid : extT1 ∈ coherentGrid extIndex extMesh.d 1 ∅ 2 := by
  unfold coherentGrid
  rw [Finset.mem_image]
  refine ⟨extC', ?_, ?_⟩
  · unfold worldWeights
    rw [Finset.mem_filter]
    refine ⟨Fintype.mem_piFinset.mpr fun _ => Finset.mem_univ _, ?_, ?_⟩
    · simp only [extC'_val, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    · intro u _ φ hφ; simp at hφ
  · funext ⟨φ, hφ⟩
    unfold marginalOf extT1
    have hval : ∀ u : FiniteWorld 2, (((extC' u).val : ℕ) : ℚ) / (extMesh.d 1 : ℚ) =
        (if u = wPnQ then 1 / 2 else 0) + (if u = wnPQ then 1 / 2 else 0) := by
      intro u
      rw [extC'_val]
      show _ / ((2 : ℕ) : ℚ) = _
      split_ifs <;> norm_num
    simp only [hval, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [extIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with rfl | rfl | rfl
    · rw [payout_wPnQ_p, payout_wnPQ_p]; simp
    · rw [payout_wPnQ_q, payout_wnPQ_q]; simp
    · rw [payout_wPnQ_pq, payout_wnPQ_pq]; simp

/-- **P2.** `extT1 ∈ faceGen (coherentGrid …) extT` via the point mass at `extT1`: the
coherent-grid face over `extT` is nonempty, so `faceGen_coherentGrid_not_prod` is about a
nonempty face. -/
theorem extT1_mem_faceGen : extT1 ∈ faceGen (coherentGrid extIndex extMesh.d 1 ∅ 2) extT := by
  rw [mem_faceGen_iff]
  refine ⟨extT1_mem_coherentGrid, fun Q => if Q = extT1 then 1 else 0, ⟨?_, ?_, ?_⟩, ?_, by simp⟩
  · intro Q; dsimp only; split_ifs <;> norm_num
  · intro Q hQ; dsimp only; rw [if_neg]; rintro rfl; exact hQ extT1_mem_coherentGrid
  · rw [Finset.sum_ite_eq', if_pos extT1_mem_coherentGrid]
  · funext φ
    rw [Table.restrict_apply]
    unfold meanOn
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos extT1_mem_coherentGrid]
    rfl

/-! ## P3 — `D ≠ ∅` is inhabited, and `D` bites -/

/-- The two-atom index `{p, q}`. -/
def dIndex : SmallIndex := ⟨fun _ => {pA, qA}, fun _ => Finset.Subset.refl _⟩

/-- The table `(p ↦ 1, q ↦ 1/2)`. -/
def dT : Table dIndex 0 := fun φ => if φ.1 = pA then 1 else 1 / 2

/-- Weights `1/2` on `p ∧ q` and `1/2` on `p ∧ ¬q` (both consistent with `D = {p}`). -/
def dW (u : FiniteWorld 2) : ℚ := (if u = wPQ then 1 / 2 else 0) + (if u = wPnQ then 1 / 2 else 0)

lemma payout_wPQ_p : wPQ.payoutRat pA = 1 := by decide
lemma payout_wPQ_q : wPQ.payoutRat qA = 1 := by decide

/-- **P3(a).** `(1, 1/2)` is coherent relative to `D = {p}` with `B = 2`: the `D`-relativized
definition is inhabited with `D ≠ ∅`. -/
theorem dT_coherent_D : CoherentOn dT {pA} 2 := by
  refine ⟨dW, ?_, ?_, ?_, ?_⟩
  · intro u; unfold dW; split_ifs <;> norm_num
  · unfold dW
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]; norm_num
  · intro u hu φ hφ
    rw [Finset.mem_singleton] at hφ; subst hφ
    unfold dW at hu
    by_cases h1 : u = wPQ
    · subst h1; exact holds_of_payoutRat_eq_one payout_wPQ_p
    · by_cases h2 : u = wPnQ
      · subst h2; exact holds_of_payoutRat_eq_one payout_wPnQ_p
      · exfalso; simp [h1, h2] at hu
  · rintro ⟨φ, hφ⟩
    simp only [dIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
    have e : ∀ χ : Sentence, ∑ u, dW u * u.payoutRat χ =
        1 / 2 * wPQ.payoutRat χ + 1 / 2 * wPnQ.payoutRat χ := by
      intro χ; unfold dW
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [e]
    rcases hφ with rfl | rfl
    · rw [payout_wPQ_p, payout_wPnQ_p]; norm_num [dT]
    · rw [payout_wPQ_q, payout_wPnQ_q]
      norm_num [dT, show qA ≠ pA from fun h => by cases h]

/-- The table `(p ↦ 1/2, q ↦ 1/2)`. -/
def dT' : Table dIndex 0 := fun _ => 1 / 2

/-- **P3(b).** `(1/2, 1/2)` is coherent at `D = ∅` (weights `1/2` on `p ∧ q`, `1/2` on
`¬p ∧ ¬q`)… -/
theorem dT'_coherent_empty : CoherentOn dT' ∅ 2 := by
  refine ⟨fun u => (if u = wPQ then 1 / 2 else 0) + (if u = wnPnQ then 1 / 2 else 0),
    ?_, ?_, ?_, ?_⟩
  · intro u; dsimp only; split_ifs <;> norm_num
  · simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]; norm_num
  · intro u _ φ hφ; simp at hφ
  · rintro ⟨φ, hφ⟩
    simp only [dIndex, Finset.mem_insert, Finset.mem_singleton] at hφ
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rcases hφ with rfl | rfl
    · rw [payout_wPQ_p, payout_wnPnQ pA (by simp [extIndex])]; norm_num [dT']
    · rw [payout_wPQ_q, payout_wnPnQ qA (by simp [extIndex])]; norm_num [dT']

/-- **P3(c).** …and not at `D = {p}`: every `D`-consistent world holds `p`, so the price of
`p` must be `1`. The `D`-relativization is not decorative. -/
theorem dT'_not_coherent_D : ¬ CoherentOn dT' {pA} 2 := by
  rintro ⟨w, hw0, hw1, hwD, ht⟩
  have h := ht ⟨pA, by simp [dIndex]⟩
  have : ∑ u, w u * u.payoutRat pA = ∑ u, w u := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : w u = 0
    · rw [hu, zero_mul]
    · rw [payoutRat_of_holds (hwD u hu pA (Finset.mem_singleton_self _)), mul_one]
  rw [this, hw1] at h
  unfold dT' at h
  norm_num at h

/-! ## P4 — `hB` is load-bearing -/

/-- The atom `r = atom 5`, beyond the bound `B = 0`. -/
def r5 : Sentence := Formula.atom 5

/-- **P4.** With `A = ∅`, `D = {atom 5}` and `B = 0`, the indicator of the all-true world
satisfies the two axioms plus non-negativity relative to `D`, yet is no world marginal on
`FiniteWorld 0`: the single finite world reads atom 5 as `false`, so no world is
`D`-consistent and no weight can sum to `1`. So `twoAxiom_iff_worldMarginal` is **false**
without `hB`, and the hypothesis is doing real work (mandate design decision 8's trap). -/
theorem hB_needed :
    ∃ V : Sentence → ℚ, TwoAxiomCoherent V ∅ {r5} ∧ ¬ IsWorldMarginal V ∅ {r5} 0 := by
  have hcons : trueWorld.ConsistentWith {r5} := by
    intro ψ hψ
    rw [Finset.mem_singleton] at hψ; subst hψ
    simp [trueWorld, r5]
  refine ⟨indQ trueWorld, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro φ _; unfold indQ; split_ifs <;> norm_num
  · intro φ _ ht
    unfold indQ; rw [if_pos (ht trueWorld hcons)]
  · intro φ ψ _ _ hc
    exact indQ_or_of_disjoint _ (hc trueWorld hcons)
  · rintro ⟨w, -, hw1, hwD, -⟩
    have hz : ∀ u : FiniteWorld 0, w u = 0 := by
      intro u
      by_contra h
      have := hwD u h r5 (Finset.mem_singleton_self _)
      simp [worldOf, FiniteWorld.toBoolPCWorld, BoolPCWorld.toPCWorld, r5] at this
    rw [Finset.sum_eq_zero (fun u _ => hz u)] at hw1
    exact zero_ne_one hw1

/-! ## P5 — `Balanced` is a real constraint -/

/-- **P5.** The point mass at `Q₂ = (p ↦ 0, q ↦ 1/2)` is a grid probability and is **not**
balanced at `t₀ = (p ↦ 1/2)`: `Kernel.balanced` excludes point-mass kernels at a fixed table. -/
theorem pointMass_not_balanced :
    IsProb witMesh.d (fun Q => if Q = Q₂ then (1 : ℚ) else 0) ∧
    ¬ Balanced witMesh.d (fun Q => if Q = Q₂ then (1 : ℚ) else 0) t₀ := by
  refine ⟨⟨fun Q => by dsimp only; split_ifs <;> norm_num,
    fun Q hQ => by dsimp only; rw [if_neg]; rintro rfl; exact hQ Q₂_mem_grid,
    by rw [Finset.sum_ite_eq', if_pos Q₂_mem_grid]⟩, ?_⟩
  intro hb
  have h := hb ⟨pW, pW_mem_S0⟩
  rw [Table.restrict_apply] at h
  unfold mean meanOn at h
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos Q₂_mem_grid] at h
  unfold Q₂ t₀ at h
  norm_num at h

/-! ## P6 — `t.InUnit` is load-bearing in `faceProd_eq_faceGen` -/

/-- Off the unit cube (`t = (p ↦ 2)`) the generated face is empty… -/
theorem faceGen_empty_off_cube :
    faceGen (grid witIndex witMesh.d 1) (fun _ => (2 : ℚ)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro Q hQ
  obtain ⟨-, F, hF, hb, -⟩ := mem_faceGen_iff.mp hQ
  have h := congrFun hb ⟨pW, pW_mem_S0⟩
  rw [Table.restrict_apply] at h
  have hle := (hF.meanOn_mem_Icc (fun _ hQ => inUnit_of_mem_grid hQ)
    ⟨pW, witIndex.mono 0 pW_mem_S0⟩).2
  rw [h] at hle
  norm_num at hle

/-- …while the product face is the whole (nonempty) grid, since nothing is pinned. -/
theorem faceProd_nonempty_off_cube :
    (faceProd witIndex witMesh.d 0 (fun _ => (2 : ℚ))).Nonempty :=
  ⟨fun _ => 0, mem_faceProd_iff.mpr ⟨mem_grid_iff.mpr fun _ => zero_mem_gridVals _,
    fun _ h => by norm_num at h⟩⟩

/-! ## P7 — the degenerate index -/

/-- The index with no small sentences on any day. -/
def emptyIndex : SmallIndex := ⟨fun _ => ∅, fun _ => Finset.Subset.refl _⟩

/-- **P7.** On the empty index every superbelief is balanced at every table: the theorems of
the package say nothing there. The T9 witness (`|S 1| = 2`, `d = 2`) is what excludes this. -/
theorem balanced_vacuous_on_emptyIndex (d : ℕ → ℕ) (F : Superbelief emptyIndex 1)
    (t : Table emptyIndex 0) : Balanced d F t :=
  fun φ => absurd φ.2 (Finset.notMem_empty _)

end Cleanroom.Bli.BliFinite.AuditR1
