import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesE
import Cleanroom.Corrigibility.CorrReflectFrames.Dominance

/-!
# corr-reflect-frames — witnesses F (repair round 1): Good's theorem, VOI, the both-zero builder

* **T10(b)**, `reflection.py` T4 (`good_voi_7_20`): eight worlds `(1,3,2,4,1,2,5,2)/20`, the
  partition `{1,2,3}{4,5}{6,7,8}`, the act with payoff `X = (3,1,1,−1,2,−2,1,−3)` against
  abstaining: `max_a E_π(u a) = 1/20` while `∑_w π w · max_a E_{P_w}(u a) = 2/5` — value of
  information `7/20 > 0` with estimate matching exact (`E_π E_{P_w} X = E_π X = 1/20`).
* **T10(c)**, Prop 5′ instances: revealing `θ` with probability `1/2` halves the residual VOI
  `8 → 4` (`voi_halves`); a single signal can raise it (`voi_single_signal_raises`: the
  uninformative-looking signal that flattens `(9/10, 1/10)` to `(1/2, 1/2)` raises the residual
  from `8/5` to `8`), while the expectation over the signal does not (`sum_voi_le_voi`).
* **T9(g)**, the both-zero builder (`bothZero_builder`): `ε₀ = 1/5`, `(q₁, q₀) = (9/10, 1/10)`,
  two independent signals; the fully-retaining builder's successor is the refinement along
  `(s₁, s₂)`, reflective by the selection theorem, and hands `P(W | s₁ = s₂ = 0) = 1/325 < 1/25`
  (overrides) on a branch of probability `13/20`, `P(W | disagree) = 1/5 ≥ 1/25` (complies) on
  the mixed branch; the face value of a single candidate is `1/37`.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

/-- The two-element menu is nonempty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hA2 : (univ : Finset (Fin 2)).Nonempty := ⟨0, mem_univ 0⟩

/-- `sup'` over `Fin 2` is the binary `max`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sup'_fin2 (h : (univ : Finset (Fin 2)).Nonempty) (g : Fin 2 → ℝ) :
    univ.sup' h g = max (g 0) (g 1) := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro b _
    fin_cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' g (mem_univ 0)) (le_sup' g (mem_univ 1))

/-- Expectation under a positive conditional row, as a ratio of full sums.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_E_eq {W S : Type} [Fintype W] [DecidableEq W] [DecidableEq S] {π : W → ℝ}
    {f : W → S} {w : W} (h : 0 < mass π (fibre f w)) (X : W → ℝ) :
    E (condRow π f w) X = (∑ v, if f v = f w then π v * X v else 0) / mass π (fibre f w) := by
  rw [eq_div_iff h.ne', condRow_E_mul h, fibre, sum_filter]

/-! ## T10(b): `reflection.py` T4 -/

/-- The T4 prior `(1, 3, 2, 4, 1, 2, 5, 2)/20`.
Source: [[armstrong]] `reflection.py` T4 (I6.2 l. 143, I17.2 l. 248)
Kind: D
Fidelity: exact -/
def πT4 : Fin 8 → ℝ := ![1 / 20, 3 / 20, 2 / 20, 4 / 20, 1 / 20, 2 / 20, 5 / 20, 2 / 20]

/-- Every T4 atom is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πT4_pos (w : Fin 8) : 0 < πT4 w := by fin_cases w <;> norm_num [πT4]

/-- `πT4` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πT4_nonneg (w : Fin 8) : 0 ≤ πT4 w := (πT4_pos w).le

/-- The T4 partition `{1,2,3}{4,5}{6,7,8}`.
Source: [[armstrong]] `reflection.py` (`Fpart`)
Kind: D
Fidelity: exact -/
def partT4 : Fin 8 → Fin 3 := ![0, 0, 0, 1, 1, 2, 2, 2]

/-- The T4 payoff of acting, `X = (3, 1, 1, −1, 2, −2, 1, −3)`.
Source: [[armstrong]] `reflection.py` T4
Kind: D
Fidelity: exact -/
def XT4 : Fin 8 → ℝ := ![3, 1, 1, -1, 2, -2, 1, -3]

/-- The two-act menu: act (payoff `X`) or abstain (payoff `0`).
Source: [[armstrong]] `reflection.py` T4 (`max(E_j X, 0)`)
Kind: D
Fidelity: exact -/
def uT4 : Fin 2 → Fin 8 → ℝ := ![XT4, fun _ => 0]

/-- The refinement's rows estimate `X` at `4/3`, `−2/5`, `−5/9` on the three cells.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rowT4 (w : Fin 8) : E ((refineFrame πT4 πT4_nonneg partT4).P w) XT4 =
    ![4 / 3, 4 / 3, 4 / 3, -2 / 5, -2 / 5, -5 / 9, -5 / 9, -5 / 9] w := by
  fin_cases w <;>
    (show E (condRow πT4 partT4 _) XT4 = _
     rw [condRow_E_eq (mass_fibre_pos_of_pos πT4_nonneg (πT4_pos _)), mass_fibre_eq]
     simp [Fin.sum_univ_eight, partT4, πT4, XT4] <;> norm_num)

/-- **Good's theorem, T4 instance (T10(b), N+)**: `max_a E_π(u a) = 1/20`,
`∑_w π w · max_a E_{P_w}(u a) = 2/5`, value of information `7/20 > 0`, with the refinement
estimate-matching (so `E_π E_{P_w} X = E_π X` exactly: reflection fixes the first moment and
leaves the value of the realized teaching free).
Source: [[armstrong]] `reflection.py` T4; I6.2 l. 143; I17.2 l. 248; mandate T10(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem good_voi_7_20 :
    univ.sup' hA2 (fun a => E πT4 (uT4 a)) = 1 / 20 ∧
      ∑ w, πT4 w * univ.sup' hA2 (fun a => E ((refineFrame πT4 πT4_nonneg partT4).P w) (uT4 a)) =
        2 / 5 ∧
      EstimateMatching πT4 (refineFrame πT4 πT4_nonneg partT4) ∧
      E πT4 XT4 = 1 / 20 := by
  have hX : E πT4 XT4 = 1 / 20 := by simp [E, Fin.sum_univ_eight, πT4, XT4]; norm_num
  have h0 : ∀ ρ : Fin 8 → ℝ, E ρ (fun _ => 0) = 0 := fun ρ => by simp [E]
  refine ⟨?_, ?_, refineFrame_estimateMatching _ _, hX⟩
  · rw [sup'_fin2]
    simp only [uT4, Matrix.cons_val_zero, Matrix.cons_val_one, hX, h0]
    norm_num
  · simp only [sup'_fin2, uT4, Matrix.cons_val_zero, Matrix.cons_val_one, h0, rowT4]
    simp only [Fin.sum_univ_eight, πT4, Matrix.cons_val, max_def]
    split_ifs <;> norm_num at *

/-! ## T10(c): Prop 5′ instances -/

/-- The menu `V k θ = 16 · 𝟙[k = θ]`: guess `θ` for `16`.
Source: [[joint-final]] P.5′ l. 176; mandate T10(c)
Kind: D
Fidelity: exact -/
def V16 : Fin 2 → Fin 2 → ℝ := ![![16, 0], ![0, 16]]

/-- The uniform prior on `Θ = Fin 2`.
Source: mandate T10(c)
Kind: D
Fidelity: exact -/
def πu2 : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Signal weights: no reveal with probability `1/2`, reveal `θ = 0` or `θ = 1` with `1/4` each.
Source: mandate T10(c) ("revealing `θ` w.p. `1/2`")
Kind: D
Fidelity: exact -/
def pRev : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- The posteriors: the prior, `δ₀ = (1, 0)`, `δ₁ = (0, 1)`.
Source: mandate T10(c)
Kind: D
Fidelity: exact -/
def postRev : Fin 3 → Fin 2 → ℝ := ![πu2, ![1, 0], ![0, 1]]

/-- **Revealing `θ` with probability `1/2` halves the residual VOI, `8 → 4` (T10(c), N+)**: the
posteriors form a martingale, `voi π V = 8`, and the expected residual is `4`.
Source: [[joint-final]] Prop 5′ l. 112 (remark); mandate T10(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem voi_halves :
    voi hA2 πu2 V16 = 8 ∧ (∀ θ, ∑ s, pRev s * postRev s θ = πu2 θ) ∧
      ∑ s, pRev s * voi hA2 (postRev s) V16 = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [voi, sup'_fin2, Fin.sum_univ_two, πu2, V16, Matrix.cons_val, max_def]
    split_ifs <;> norm_num at *
  · intro θ
    fin_cases θ <;> simp [Fin.sum_univ_three, pRev, postRev, πu2] <;> norm_num
  · simp only [voi, sup'_fin2, Fin.sum_univ_two, Fin.sum_univ_three, pRev, postRev, πu2, V16,
      Matrix.cons_val, max_def]
    split_ifs <;> norm_num at *

/-- The skewed prior `(9/10, 1/10)`.
Source: mandate T10(c)
Kind: D
Fidelity: exact -/
def π91 : Fin 2 → ℝ := ![9 / 10, 1 / 10]

/-- Signal weights `(1/5, 4/5)`.
Source: mandate T10(c)
Kind: D
Fidelity: exact -/
def pR : Fin 2 → ℝ := ![1 / 5, 4 / 5]

/-- Posteriors: the flattening signal gives the uniform prior, the other gives `δ₀ = (1, 0)`.
Source: mandate T10(c)
Kind: D
Fidelity: exact -/
def postR : Fin 2 → Fin 2 → ℝ := ![πu2, ![1, 0]]

/-- **A single signal can raise the residual VOI (T10(c), N+)**: under the martingale family
`(1/5 · uniform + 4/5 · δ₀ = (9/10, 1/10))`, the prior's residual is `8/5` and the flattening
signal's posterior has residual `8 > 8/5` — Prop 5′ bounds the expectation over the signal
only (`1/5 · 8 + 4/5 · 0 = 8/5`).
Source: [[joint-final]] Prop 5′ l. 112 ("a particular signal can raise it"); mandate T10(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem voi_single_signal_raises :
    voi hA2 π91 V16 = 8 / 5 ∧ (∀ θ, ∑ s, pR s * postR s θ = π91 θ) ∧
      voi hA2 (postR 0) V16 = 8 ∧ (8 / 5 : ℝ) < 8 ∧
      ∑ s, pR s * voi hA2 (postR s) V16 = 8 / 5 := by
  refine ⟨?_, ?_, ?_, by norm_num, ?_⟩
  · simp only [voi, sup'_fin2, Fin.sum_univ_two, π91, V16, Matrix.cons_val, max_def]
    split_ifs <;> norm_num at *
  · intro θ
    fin_cases θ <;> simp [Fin.sum_univ_two, pR, postR, π91, πu2] <;> norm_num
  · simp only [voi, sup'_fin2, Fin.sum_univ_two, postR, πu2, V16, Matrix.cons_val, max_def]
    split_ifs <;> norm_num at *
  · simp only [voi, sup'_fin2, Fin.sum_univ_two, pR, postR, πu2, V16, Matrix.cons_val, max_def]
    split_ifs <;> norm_num at *

/-! ## T9(g): the both-zero builder -/

/-- The both-zero prior on `(state, s₁, s₂)`: `P(W) = 1/5`, `P(s = 1 | W) = 9/10`,
`P(s = 1 | R) = 1/10`, signals independent given the state; atoms
`(324, 36, 36, 4, 1, 9, 9, 81)/500` with `W = {4, 5, 6, 7}` and `(s₁, s₂) = (x₁, x₂)`.
Source: [[joint-final]] Prop 6′ corrected l. 120, E4 l. 199; corr-wf14-062, corr-wf14-2-006
Kind: D
Fidelity: exact -/
def πBZ : Fin 8 → ℝ := ![324 / 500, 36 / 500, 36 / 500, 4 / 500, 1 / 500, 9 / 500, 9 / 500, 81 / 500]

/-- Every both-zero atom is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πBZ_pos (w : Fin 8) : 0 < πBZ w := by fin_cases w <;> norm_num [πBZ]

/-- `πBZ` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πBZ_nonneg (w : Fin 8) : 0 ≤ πBZ w := (πBZ_pos w).le

/-- The fully-retaining builder's successor: the refinement along both signals.
Source: [[joint-final]] E4 l. 199 ("a builder that conditions on everything it knows")
Kind: D
Fidelity: exact -/
def FBZ : Frame (Fin 8) := refineFrame πBZ πBZ_nonneg (fun w => (x₁ w, x₂ w))

/-- **The both-zero builder (T9(g), N+)**: the fully-retaining successor is reflected by the
prior (selection theorem); on the both-zero branch, of probability `13/20`, it announces
`P(W | s₁ = s₂ = 0) = 1/325 < 1/25` (overrides, below the compliance threshold `ε* = 1/25`);
on the disagreeing branch it announces `1/5 ≥ 1/25` (complies); the face value of the
single-signal candidate is `1/37`. Full retention does not favour compliance.
Source: [[joint-final]] Prop 6′ corrected l. 120, E4 l. 199 (threshold `1/25` l. 162);
[[joint]] E4 l. 205; corr-wf14-062, corr-wf14-2-006; mandate T9(g)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem bothZero_builder :
    Reflects πBZ FBZ ∧ mass πBZ (fibre (fun w => (x₁ w, x₂ w)) 0) = 13 / 20 ∧
      mass (FBZ.P 0) φ8 = 1 / 325 ∧ mass (FBZ.P 1) φ8 = 1 / 5 ∧
      mass (condRow πBZ x₁ 0) φ8 = 1 / 37 ∧ (1 / 325 : ℝ) < 1 / 25 ∧ (1 / 25 : ℝ) ≤ 1 / 5 := by
  refine ⟨refineFrame_reflects _ _, ?_, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · rw [mass_fibre_eq]; simp [Fin.sum_univ_eight, x₁, x₂, πBZ]; norm_num
  · show mass (condRow πBZ (fun w => (x₁ w, x₂ w)) 0) φ8 = _
    rw [condRow_mass_eq (mass_fibre_pos_of_pos πBZ_nonneg (πBZ_pos _)), mass_inter_fibre_eq',
      mass_fibre_eq]
    simp [Fin.sum_univ_eight, x₁, x₂, πBZ]; norm_num
  · show mass (condRow πBZ (fun w => (x₁ w, x₂ w)) 1) φ8 = _
    rw [condRow_mass_eq (mass_fibre_pos_of_pos πBZ_nonneg (πBZ_pos _)), mass_inter_fibre_eq',
      mass_fibre_eq]
    simp [Fin.sum_univ_eight, x₁, x₂, πBZ]; norm_num
  · rw [condRow_mass_eq (mass_fibre_pos_of_pos πBZ_nonneg (πBZ_pos _)), mass_inter_fibre_eq',
      mass_fibre_eq]
    simp [Fin.sum_univ_eight, x₁, πBZ]; norm_num

end

end Cleanroom.Corrigibility.CorrReflectFrames.Witnesses
