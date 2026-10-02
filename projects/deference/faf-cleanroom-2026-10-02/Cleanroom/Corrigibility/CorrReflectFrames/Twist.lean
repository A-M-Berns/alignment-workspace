import Cleanroom.Corrigibility.CorrReflectFrames.Selection

/-!
# corr-reflect-frames — T2: twisted estimators, and the fn 18 independence

The **twist family** `twist π f l`: rows `(1 − l) · π(· | f-cell) + l · π`. For every partition
with two `π`-positive cells and every `0 < l < 1` it is estimate-matching (Armstrong's sequential
unbiasedness in one step) and fails introspection at candidates, hence fails Reflection
(Theorem A(c)). This is the run's N+ witness that estimate matching (Mart) is strictly weaker
than Reflection without introspection — the same phenomenon as `udt-supercondition`'s
`reflective_not_calibrated_witness` (`as38`), by the bridge of `Bridge.lean`.

fn 18 (ddb): sequential unbiasedness is independent of Value in the modest setting — `fig3` is
valued and not stationary, `fig2` is stationary and not valued.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W] {S : Type} [DecidableEq S]

/-- **The twist family**: rows `(1 − l) · π(· | f = f w) + l · π`, a convex combination of the
Bayesian refinement's row and the prior (Armstrong's "twist it a bit").
Source: [[armstrong]] I2.2 l. 95 (`q_c = ⅔ P(· | c) + ⅓ P`), A2 l. 264
Kind: D
Fidelity: exact (Armstrong's `λ = ⅓` generalized to `l ∈ [0, 1]`) -/
def twist (π : W → ℝ) (hπ : π ∈ stdSimplex ℝ W) (f : W → S) (l : ℝ) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) : Frame W where
  P := fun w => (1 - l) • condRow π f w + l • π
  P_mem := fun w =>
    convex_stdSimplex ℝ W (condRow_mem hπ.1 f w) hπ (by linarith) hl0 (by ring)

/-- The rows of the twist family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem twist_P (π : W → ℝ) (hπ : π ∈ stdSimplex ℝ W) (f : W → S) (l : ℝ) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (w : W) : (twist π hπ f l hl0 hl1).P w = (1 - l) • condRow π f w + l • π := rfl

/-- **Every twist is estimate-matching**: the mixture identity `∑_c π(c) q_c = π` in one line —
estimate matching is linear in the rows and holds for the refinement and for the constant frame.
Source: [[armstrong]] I2.2 l. 95 ("satisfies `∑_c P(c) q_c = P`, hence SU for every `X`")
Kind: P
Fidelity: exact (whole family)
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem twist_estimateMatching (π : W → ℝ) (hπ : π ∈ stdSimplex ℝ W) (f : W → S) (l : ℝ)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) : EstimateMatching π (twist π hπ f l hl0 hl1) := by
  intro X
  have hR : ∑ w, π w * E (condRow π f w) X = E π X :=
    refineFrame_estimateMatching hπ.1 f X
  show ∑ w, π w * E ((1 - l) • condRow π f w + l • π) X = E π X
  simp only [E_add_left, E_smul_left, mul_add, sum_add_distrib]
  have h1 : ∑ w, π w * ((1 - l) * E (condRow π f w) X) =
      (1 - l) * ∑ w, π w * E (condRow π f w) X := by
    rw [mul_sum]; apply sum_congr rfl; intro w _; ring
  rw [h1, hR, ← sum_mul, hπ.2]
  ring

/-- **Every non-trivial twist fails introspection at candidates**: with two `π`-positive cells
`f w₁ ≠ f w₂` and `0 < l < 1`, the candidate row at `w₁` differs from the row at `w₂` (they
differ at `w₁` by `(1 − l) · π w₁ / π(cell)`), so `w₂` is outside its cell and its self-mass is
at most `1 − l · π w₂ < 1`.
Source: [[armstrong]] I2.2 l. 95 (`q_{c₁}(c₁) = 23/30 < 1`), A2 l. 264
Kind: P
Fidelity: exact (whole family)
Hyps: (a) `hπ`, two positive cells, `0 < l < 1` -/
theorem twist_not_candsIntrospective (π : W → ℝ) (hπ : π ∈ stdSimplex ℝ W) (f : W → S) {l : ℝ}
    (hl0 : 0 < l) (hl1 : l < 1) {w₁ w₂ : W} (h₁ : 0 < π w₁) (h₂ : 0 < π w₂)
    (hne : f w₁ ≠ f w₂) : ¬ CandsIntrospective π (twist π hπ f l hl0.le hl1.le) := by
  intro hINT
  set G := twist π hπ f l hl0.le hl1.le with hG
  have hc : G.P w₁ ∈ G.cands π := G.P_mem_cands h₁
  have hself := hINT _ hc
  have hm₁ : 0 < mass π (fibre f w₁) := mass_fibre_pos_of_pos hπ.1 h₁
  have hm₂ : 0 < mass π (fibre f w₂) := mass_fibre_pos_of_pos hπ.1 h₂
  have hw₂ : w₂ ∉ G.cell (G.P w₁) := by
    rw [Frame.mem_cell]
    intro heq
    have := congrFun heq w₁
    rw [hG, twist_P, twist_P] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [condRow_apply_of_pos hm₁, condRow_apply_of_pos hm₂] at this
    have hin : w₁ ∈ fibre f w₁ := mem_fibre_self f w₁
    have hnin : w₁ ∉ fibre f w₂ := by rw [mem_fibre]; exact hne
    simp only [ind, hin, hnin, if_true, if_false, one_mul, zero_mul, mul_zero, zero_div, add_zero,
      zero_add] at this
    have : 0 < (1 - l) * (π w₁ / mass π (fibre f w₁)) :=
      mul_pos (by linarith) (div_pos h₁ hm₁)
    linarith
  have hcell_le : mass π (G.cell (G.P w₁)) ≤ 1 - π w₂ := by
    have hsplit := mass_inter_add_mass_sdiff π univ (G.cell (G.P w₁))
    have h2 : π w₂ ≤ mass π (univ \ G.cell (G.P w₁)) :=
      single_le_sum (fun v _ => hπ.1 v) (by simp [hw₂])
    rw [univ_inter, mass_univ hπ] at hsplit
    linarith
  have hr_le : mass (condRow π f w₁) (G.cell (G.P w₁)) ≤ 1 :=
    mass_le_one (condRow_mem hπ.1 f w₁) _
  have hexp : G.selfMass (G.P w₁) =
      (1 - l) * mass (condRow π f w₁) (G.cell (G.P w₁)) + l * mass π (G.cell (G.P w₁)) := by
    unfold Frame.selfMass
    rw [hG, twist_P]
    simp only [mass, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, mul_sum]
  rw [hexp] at hself
  have e1 : (1 - l) * mass (condRow π f w₁) (G.cell (G.P w₁)) ≤ (1 - l) * 1 :=
    mul_le_mul_of_nonneg_left hr_le (by linarith)
  have e2 : l * mass π (G.cell (G.P w₁)) ≤ l * (1 - π w₂) :=
    mul_le_mul_of_nonneg_left hcell_le hl0.le
  have := mul_pos hl0 h₂
  linarith

/-- **Every non-trivial twist fails Reflection** (Theorem A(c) contrapositive): estimate matching
without introspection. The run's N+ separation of (Mart) from (R-fun) without INT.
Source: [[armstrong]] I2.2 l. 95 (`ρ_i({1} | ρ_j = q_{c₁}) = 1/6 ≠ 23/180`), A2 l. 264;
[[radical]] Theorem I4.1 remark "without INT the two forms separate"
Kind: P
Fidelity: exact (whole family)
Hyps: (a) `hπ`, two positive cells, `0 < l < 1` -/
theorem twist_not_reflects (π : W → ℝ) (hπ : π ∈ stdSimplex ℝ W) (f : W → S) {l : ℝ}
    (hl0 : 0 < l) (hl1 : l < 1) {w₁ w₂ : W} (h₁ : 0 < π w₁) (h₂ : 0 < π w₂)
    (hne : f w₁ ≠ f w₂) : ¬ Reflects π (twist π hπ f l hl0.le hl1.le) :=
  fun h => twist_not_candsIntrospective π hπ f hl0 hl1 h₁ h₂ hne
    (candsIntrospective_of_reflects hπ.1 h)

/-! ## fn 18: sequential unbiasedness is independent of Value (modest setting) -/

open Cleanroom.Found.LitDdbFrames.Examples in
/-- **fn 18, first half.** DDB's Figure 3 is valued by the uniform deferrer and *not*
stationary: `πP = (11/20, 9/20) ≠ (1/2, 1/2)`.
Source: [[ddb]] iteration item l. 149 (fn 18: "Figure 3 is valued and not stationary")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig3_value_not_estimateMatching : Value half fig3 ∧ ¬ EstimateMatching half fig3 := by
  refine ⟨fig3_totalTrust_value.2, ?_⟩
  rw [estimateMatching_iff_stationary]
  intro h
  have := h 0
  norm_num [Fin.sum_univ_two, half, fig3_P0, fig3_P1] at this

open Cleanroom.Found.LitDdbFrames.Examples in
/-- **fn 18, second half.** DDB's Figure 2 (the anti-expert) is stationary under the uniform
deferrer and *not* valued. With `fig3_value_not_estimateMatching`: in the modest setting
sequential unbiasedness is neither necessary nor sufficient for Value (finding for
corr-wf13-095).
Source: [[ddb]] iteration item l. 149 (fn 18: "the anti-expert frame is stationary and not
valued")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig2_estimateMatching_not_value : EstimateMatching half fig2 ∧ ¬ Value half fig2 := by
  refine ⟨?_, fig2_not_value⟩
  rw [estimateMatching_iff_stationary]
  intro w'
  fin_cases w' <;> norm_num [Fin.sum_univ_two, half, fig2_P0, fig2_P1]

end

end Cleanroom.Corrigibility.CorrReflectFrames
