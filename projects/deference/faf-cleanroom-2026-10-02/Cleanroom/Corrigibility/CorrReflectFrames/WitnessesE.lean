import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesD

/-!
# corr-reflect-frames — witnesses E (repair round 1): the depth-2 coin tree

`W = Fin 8` encodes `(θ, x₁, x₂)` with `θ ∈ {1/3, 2/3}` uniform (index `θ·4 + x₁·2 + x₂`,
`θ = 1 ↦ 2/3`) and two i.i.d. flips with `P(x = 1 | θ) = θ`; prior
`π8 = (8, 4, 4, 2, 2, 4, 4, 8)/36`, `φ = {θ = 2/3} = {4, 5, 6, 7}`. Every atom is positive: no
null cells anywhere in this file.

* **T9(b), the path-maximum refutation** (`pathMax_not_estimateMatching`): the rule that stops
  at the time `m ∈ {0, 1, 2}` maximizing `P(φ | first m flips)` along the path selects among the
  refinements `ℱ_m` without retaining its grounds, and `E[P_τ(φ)] = 67/108 ≠ 1/2` — the depth-2
  instance of radical `s3`'s `353/540`.
* **T9(c), Sel.2** (`faceValue_not_valueReflectsOn`): with candidates `ρᵢ = P(φ | Xᵢ)` and
  "adopt the larger", `E[ρ_σ] = 31/54 ≠ 1/2` and `P(φ | ρ_σ = 2/3) = 8/13 ≠ 2/3`; the retained
  successor `P(φ | σ, X_σ)` is the refinement along `w ↦ (σ w, X_{σ w} w)`, reflective by the
  selection theorem, and announces `1/2` where the face-value successor announced `2/3`.
* **T7, positive witness** (`compose_positive_witness`): `F₂ = P(· | X₁)`,
  `F₃ = P(· | X₁, X₂)`, `L₁₂ = {X₁ = 1}`, `L₂₃ = {X₂ = 1}` — function form conditional on `L₁₂`,
  value-form legitimacy of `L₂₃` by each `t₂`-candidate's lights, and the composite
  `L₁₂ ∩ L₂₃ = {3, 7}` legitimizing, with `F₃` strictly finer than `F₂` and non-trivial value
  cells at both steps.
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

/-- Mass of an event inside a fibre as a full sum with a conjunctive condition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_fibre_eq' {W S : Type} [Fintype W] [DecidableEq W] [DecidableEq S]
    (π : W → ℝ) (A : Finset W) (f : W → S) (w : W) :
    mass π (A ∩ fibre f w) = ∑ v, if v ∈ A ∧ f v = f w then π v else 0 := by
  have e : A ∩ fibre f w = univ.filter (fun v => v ∈ A ∧ f v = f w) := by
    ext v; simp [mem_fibre]
  rw [mass, e, sum_filter]

/-- Mass as a full sum with a membership condition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_eq_sum_ite {W : Type} [Fintype W] [DecidableEq W] (π : W → ℝ) (A : Finset W) :
    mass π A = ∑ w, if w ∈ A then π w else 0 := by
  rw [mass, sum_ite_mem, univ_inter]

/-! ## The tree -/

/-- The depth-2 tree prior `(8, 4, 4, 2, 2, 4, 4, 8)/36`.
Source: [[radical]] `s3` (depth 2); mandate T9(b)
Kind: D
Fidelity: exact -/
def π8 : Fin 8 → ℝ := ![8 / 36, 4 / 36, 4 / 36, 2 / 36, 2 / 36, 4 / 36, 4 / 36, 8 / 36]

/-- Every atom of the tree is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π8_pos (w : Fin 8) : 0 < π8 w := by fin_cases w <;> norm_num [π8]

/-- `π8` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π8_nonneg (w : Fin 8) : 0 ≤ π8 w := (π8_pos w).le

/-- `π8` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π8_mem : π8 ∈ stdSimplex ℝ (Fin 8) :=
  ⟨π8_nonneg, by simp [Fin.sum_univ_eight, π8]; norm_num⟩

/-- The first flip.
Source: [[radical]] `s3`
Kind: D
Fidelity: exact -/
def x₁ : Fin 8 → Fin 2 := ![0, 0, 1, 1, 0, 0, 1, 1]

/-- The second flip.
Source: [[radical]] `s3`
Kind: D
Fidelity: exact -/
def x₂ : Fin 8 → Fin 2 := ![0, 1, 0, 1, 0, 1, 0, 1]

/-- `φ = {θ = 2/3} = {4, 5, 6, 7}`.
Source: [[radical]] `s3`
Kind: D
Fidelity: exact -/
abbrev φ8 : Finset (Fin 8) := {4, 5, 6, 7}

/-- `π8(φ) = 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_π8_φ8 : mass π8 φ8 = 1 / 2 := by
  rw [mass_eq_sum_ite]; simp [Fin.sum_univ_eight, π8]; norm_num

/-- The filtration `ℱ_m = σ(first m flips)`, `m ∈ {0, 1, 2}`, as partition maps.
Source: [[radical]] `s3`; [[selection]] R1.3
Kind: D
Fidelity: exact -/
def flips2 : Fin 3 → Fin 8 → Fin 2 × Fin 2 :=
  ![fun _ => (0, 0), fun w => (x₁ w, 0), fun w => (x₁ w, x₂ w)]

/-! ## T9(b): the path-maximum rule -/

/-- The path-maximum rule: stop at the `m` maximizing `P(φ | first m flips)` along the path
(`(1,1) ↦ 2` with `4/5`; `(1,0) ↦ 1` with `2/3`; `(0,·) ↦ 0` with `1/2`, ties to the earliest).
Source: [[radical]] `s3` (the path-maximum rule); [[selection]] R2.2(i); mandate T9(b)
Kind: D
Fidelity: exact (depth 2) -/
def τmax : Fin 8 → Fin 3 := ![0, 0, 1, 2, 0, 0, 1, 2]

/-- The path-maximum frame.
Source: mandate T9(b)
Kind: D
Fidelity: exact -/
def Fmax : Frame (Fin 8) := selectFrame π8 π8_nonneg flips2 τmax

/-- The path-maximum rule does not retain its grounds: world `3` is `ℱ_0`-indistinguishable
from world `0` (which stops at `0`) but stops at `2`.
Source: [[selection]] R2.1 l. 47 (retention), R2.2(i)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem τmax_not_retains : ¬ RetainsGrounds flips2 τmax := by
  intro h
  have := h 0 0 3 rfl rfl
  simp [τmax] at this

/-- The announced values of the path-maximum frame: `(1/2, 1/2, 2/3, 4/5, 1/2, 1/2, 2/3, 4/5)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Fmax_row (w : Fin 8) :
    mass (Fmax.P w) φ8 = ![1 / 2, 1 / 2, 2 / 3, 4 / 5, 1 / 2, 1 / 2, 2 / 3, 4 / 5] w := by
  fin_cases w <;>
    (show mass (condRow π8 (flips2 (τmax _)) _) φ8 = _
     rw [condRow_mass_eq (mass_fibre_pos_of_pos π8_nonneg (π8_pos _)), mass_inter_fibre_eq',
       mass_fibre_eq]
     simp [Fin.sum_univ_eight, flips2, τmax, x₁, x₂, π8] <;> norm_num)

/-- **The path-maximum refutation (T9(b), N+)**: `E[P_τ(φ)] = 67/108 ≠ 1/2 = π(φ)`, so the
path-maximum frame is not estimate-matching, hence not reflected — selection among the
refinements `ℱ_m` without retention breaks Reflection (the depth-2 instance of `353/540`).
Source: [[radical]] `s3` (`353/540`); [[selection]] R2.2(i) l. 51; mandate T9(b)
Kind: N+
Fidelity: variant: depth 2 (`67/108`) in place of depth 3 (`353/540`)
Hyps: (a) none -/
theorem pathMax_not_estimateMatching :
    ¬ EstimateMatching π8 Fmax ∧ ¬ Reflects π8 Fmax ∧
      ∑ w, π8 w * mass (Fmax.P w) φ8 = 67 / 108 := by
  have hsum : ∑ w, π8 w * mass (Fmax.P w) φ8 = 67 / 108 := by
    simp only [Fmax_row]
    simp [Fin.sum_univ_eight, π8]; norm_num
  have hEM : ¬ EstimateMatching π8 Fmax := by
    intro h
    have := h (ind φ8)
    simp only [E_ind] at this
    rw [hsum, mass_π8_φ8] at this
    norm_num at this
  exact ⟨hEM, fun h => hEM (estimateMatching_of_varReflects (varReflects_of_reflects π8_nonneg h)),
    hsum⟩

/-! ## T9(c): face value breaks, retention restores (Sel.2) -/

/-- The two single-flip candidates `ρᵢ = P(· | Xᵢ)`, indexed by `Fin 2`.
Source: [[radical]] Sel.2 l. 344; mandate T9(c)
Kind: D
Fidelity: exact -/
def fX : Fin 2 → Fin 8 → Fin 2 := ![x₁, x₂]

/-- "Adopt the larger": select `X₁` unless `X₁ = 0 < X₂` (ties to `X₁`).
Source: [[radical]] Sel.2 l. 344
Kind: D
Fidelity: exact -/
def σ2 : Fin 8 → Fin 2 := ![0, 1, 0, 0, 0, 1, 0, 0]

/-- The face-value frame: the selected candidate's row, unconditioned on the selection.
Source: [[radical]] Sel.2 l. 344
Kind: D
Fidelity: exact -/
def Fσ : Frame (Fin 8) := selectFrame π8 π8_nonneg fX σ2

/-- The announced values of the face-value frame: `1/3` where `X₁ = 0 = X₂`, `2/3` elsewhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Fσ_row (w : Fin 8) :
    mass (Fσ.P w) φ8 = ![1 / 3, 2 / 3, 2 / 3, 2 / 3, 1 / 3, 2 / 3, 2 / 3, 2 / 3] w := by
  fin_cases w <;>
    (show mass (condRow π8 (fX (σ2 _)) _) φ8 = _
     rw [condRow_mass_eq (mass_fibre_pos_of_pos π8_nonneg (π8_pos _)), mass_inter_fibre_eq',
       mass_fibre_eq]
     simp [Fin.sum_univ_eight, fX, σ2, x₁, x₂, π8] <;> norm_num)

/-- "Adopt the larger" does not retain its grounds: world `0` selects `X₁`, and world `1` is
`X₁`-indistinguishable from it (both have `X₁ = 0`) but selects `X₂`.
Source: [[selection]] R2.1 l. 47
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem σ2_not_retains : ¬ RetainsGrounds fX σ2 := by
  intro h
  have := h 0 0 1 rfl (by simp [fX, x₁])
  simp [σ2] at this

/-- The retained successor `P(· | σ, X_σ)`: the refinement along `w ↦ (σ w, X_{σ w} w)`.
Source: [[radical]] Sel.2 l. 344 ("the retained successor … is reflective")
Kind: D
Fidelity: exact -/
def Fret : Frame (Fin 8) := refineFrame π8 π8_nonneg (fun w => (σ2 w, fX (σ2 w) w))

/-- **Sel.2 (T9(c), N+)**: the face-value frame has `E[ρ_σ] = 31/54 ≠ 1/2` (not
estimate-matching, not reflected) and `P(φ | ρ_σ = 2/3) = 8/13 ≠ 2/3` (not value-reflective for
`φ`); the retained successor is reflected by the selection theorem and announces `1/2` at world
`1` where the face-value successor announced `2/3`.
Source: [[radical]] Sel.2 l. 344 (`31/54`, `8/13`); [[selection]] R2.2(i); mandate T9(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem faceValue_not_valueReflectsOn :
    ¬ EstimateMatching π8 Fσ ∧ ¬ Reflects π8 Fσ ∧ ¬ ValueReflectsOn π8 Fσ φ8 ∧
      ∑ w, π8 w * mass (Fσ.P w) φ8 = 31 / 54 ∧
      Reflects π8 Fret ∧ mass (Fret.P 1) φ8 = 1 / 2 ∧ mass (Fσ.P 1) φ8 = 2 / 3 := by
  have hsum : ∑ w, π8 w * mass (Fσ.P w) φ8 = 31 / 54 := by
    simp only [Fσ_row]
    simp [Fin.sum_univ_eight, π8]; norm_num
  have hEM : ¬ EstimateMatching π8 Fσ := by
    intro h
    have := h (ind φ8)
    simp only [E_ind] at this
    rw [hsum, mass_π8_φ8] at this
    norm_num at this
  have hV : ¬ ValueReflectsOn π8 Fσ φ8 := by
    intro h
    have := h (2 / 3)
    rw [mass_inter_valCell, mass_valCell] at this
    simp only [Fσ_row] at this
    simp [Fin.sum_univ_eight, sum_insert, mem_insert, mem_singleton, π8] at this
    norm_num at this
  have hret : mass (Fret.P 1) φ8 = 1 / 2 := by
    show mass (condRow π8 (fun w => (σ2 w, fX (σ2 w) w)) 1) φ8 = _
    rw [condRow_mass_eq (mass_fibre_pos_of_pos π8_nonneg (π8_pos _)), mass_inter_fibre_eq',
      mass_fibre_eq]
    simp [Fin.sum_univ_eight, fX, σ2, x₁, x₂, π8]; norm_num
  refine ⟨hEM, fun h => hEM (estimateMatching_of_varReflects (varReflects_of_reflects π8_nonneg h)),
    hV, hsum, refineFrame_reflects _ _, hret, ?_⟩
  rw [Fσ_row]; simp

/-! ## T7: the positive composition witness -/

/-- `F₂ = P(· | X₁)`.
Source: [[radical]] I5.6(c) l. 175; mandate T7
Kind: D
Fidelity: exact -/
def F₂t : Frame (Fin 8) := refineFrame π8 π8_nonneg x₁

/-- `F₃ = P(· | X₁, X₂)`, strictly finer than `F₂`.
Source: [[radical]] I5.6(c) l. 175; mandate T7
Kind: D
Fidelity: exact -/
def F₃t : Frame (Fin 8) := refineFrame π8 π8_nonneg (fun w => (x₁ w, x₂ w))

/-- `L₁₂ = {X₁ = 1} = {2, 3, 6, 7}`.
Source: mandate T7
Kind: D
Fidelity: exact -/
abbrev L₁₂t : Finset (Fin 8) := {2, 3, 6, 7}

/-- `L₂₃ = {X₂ = 1} = {1, 3, 5, 7}`.
Source: mandate T7
Kind: D
Fidelity: exact -/
abbrev L₂₃t : Finset (Fin 8) := {1, 3, 5, 7}

/-- On `L₁₂`, `X₁ = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem x₁_L₁₂ (w : Fin 8) (hw : w ∈ L₁₂t) : x₁ w = 1 := by
  fin_cases w <;> simp at hw <;> rfl

/-- The `X₁`-fibre of a world of `L₁₂` is `L₁₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fibre_x₁_L₁₂ (w : Fin 8) (hw : w ∈ L₁₂t) : fibre x₁ w = L₁₂t := by
  ext v
  rw [mem_fibre, x₁_L₁₂ w hw]
  fin_cases v <;> simp [x₁]

/-- `π8(X₁ = 1) = 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_x₁_L₁₂ (w : Fin 8) (hw : w ∈ L₁₂t) : mass π8 (fibre x₁ w) = 1 / 2 := by
  rw [fibre_x₁_L₁₂ w hw, mass_eq_sum_ite]
  simp [Fin.sum_univ_eight, π8]; norm_num

/-- The cells of `F₂` at worlds of `L₁₂` lie in `L₁₂`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem F₂t_cells_L₁₂ : ∀ w ∈ L₁₂t, F₂t.cell (F₂t.P w) ⊆ L₁₂t := by
  intro w hw
  rw [show F₂t.P w = condRow π8 x₁ w from rfl, F₂t,
    cell_condRow π8_nonneg (mass_fibre_pos_of_pos π8_nonneg (π8_pos w)), fibre_x₁_L₁₂ w hw]

/-- The rows of `F₂` are the conditional rows along `X₁`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem F₂t_P (w : Fin 8) : F₂t.P w = condRow π8 x₁ w := rfl

/-- The row of `F₂` at a world of `L₁₂`, pointwise: `π8 v / (1/2)` on `X₁ = 1`, `0` off it.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_x₁_apply (w : Fin 8) (hw : w ∈ L₁₂t) (v : Fin 8) :
    condRow π8 x₁ w v = if x₁ v = 1 then π8 v / (1 / 2) else 0 := by
  rw [condRow_apply_of_pos (mass_fibre_pos_of_pos π8_nonneg (π8_pos w)), mass_fibre_x₁_L₁₂ w hw]
  simp only [ind, mem_fibre, x₁_L₁₂ w hw]
  split_ifs <;> simp

/-- The announced values of `F₃`: `(1/5, 1/2, 1/2, 4/5, 1/5, 1/2, 1/2, 4/5)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem F₃t_row (w : Fin 8) :
    mass (F₃t.P w) φ8 = ![1 / 5, 1 / 2, 1 / 2, 4 / 5, 1 / 5, 1 / 2, 1 / 2, 4 / 5] w := by
  fin_cases w <;>
    (show mass (condRow π8 (fun w => (x₁ w, x₂ w)) _) φ8 = _
     rw [condRow_mass_eq (mass_fibre_pos_of_pos π8_nonneg (π8_pos _)), mass_inter_fibre_eq',
       mass_fibre_eq]
     simp [Fin.sum_univ_eight, x₁, x₂, π8] <;> norm_num)

/-- The announced values of `F₂`: `1/3` where `X₁ = 0`, `2/3` where `X₁ = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem F₂t_row (w : Fin 8) :
    mass (F₂t.P w) φ8 = ![1 / 3, 1 / 3, 2 / 3, 2 / 3, 1 / 3, 1 / 3, 2 / 3, 2 / 3] w := by
  fin_cases w <;>
    (show mass (condRow π8 x₁ _) φ8 = _
     rw [condRow_mass_eq (mass_fibre_pos_of_pos π8_nonneg (π8_pos _)), mass_inter_fibre_eq',
       mass_fibre_eq]
     simp [Fin.sum_univ_eight, x₁, π8] <;> norm_num)

/-- **Step two of the positive witness**: every candidate of `π8` restricted to `L₁₂` (there is
one, `P(· | X₁ = 1)`) finds `L₂₃` legitimizing for `φ` toward `F₃`.
Source: [[radical]] I5.6(c) l. 175; mandate T7
Kind: L
Fidelity: n/a -/
theorem F₂t_cands_legit :
    ∀ ρ ∈ F₂t.cands (restrict π8 L₁₂t), LegitimizingVal ρ F₃t φ8 L₂₃t := by
  intro ρ hρ
  obtain ⟨w, hw, rfl⟩ := Frame.mem_cands.1 hρ
  have hwL : w ∈ L₁₂t := by
    by_contra hn
    rw [restrict_apply, if_neg hn] at hw
    exact lt_irrefl _ hw
  intro c
  rw [mass_inter_valCell, mass_inter_valCell]
  have e : φ8 ∩ L₂₃t = {5, 7} := by decide
  rw [e]
  simp only [F₃t_row, F₂t_P, condRow_x₁_apply w hwL]
  simp [sum_insert, mem_insert, mem_singleton, x₁, π8]
  split_ifs <;> (try subst_vars) <;> norm_num at *

/-- **Composition, positive witness (T7, N+)**: on the depth-2 tree with `F₂ = P(· | X₁)`,
`F₃ = P(· | X₁, X₂)`, `L₁₂ = {X₁ = 1}`, `L₂₃ = {X₂ = 1}`: function form conditional on `L₁₂`
holds, `L₂₃` is legitimizing for `φ` by the lights of each `t₂`-candidate of the restricted
deferrer, and the composite `L₁₂ ∩ L₂₃ = {3, 7}` is legitimizing for `φ` toward `F₃` — the
full hypothesis package of `legitimizingVal_compose` with proper events at both steps, `F₃`
strictly finer than `F₂` (`F₃.P 3 ≠ F₂.P 3`), and non-trivial value cells at both steps
(`F₃.P 3 ≠ F₃.P 2`, `F₂.P 2 ≠ F₂.P 0`).
Source: [[radical]] I5.6(c) l. 175; [[joint-final]] Prop 7 l. 128; mandate T7; audit r1 N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem compose_positive_witness :
    Reflects (restrict π8 L₁₂t) F₂t ∧
      (∀ ρ ∈ F₂t.cands (restrict π8 L₁₂t), LegitimizingVal ρ F₃t φ8 L₂₃t) ∧
      LegitimizingVal π8 F₃t φ8 (L₁₂t ∩ L₂₃t) ∧ L₁₂t ∩ L₂₃t = {3, 7} ∧
      F₃t.P 3 ≠ F₂t.P 3 ∧ F₃t.P 3 ≠ F₃t.P 2 ∧ F₂t.P 2 ≠ F₂t.P 0 := by
  have h₁₂ : Reflects (restrict π8 L₁₂t) F₂t :=
    reflects_restrict_of_cells_subset π8_nonneg (refineFrame_reflects _ _) F₂t_cells_L₁₂
  refine ⟨h₁₂, F₂t_cands_legit, legitimizingVal_compose π8_nonneg h₁₂ F₂t_cands_legit,
    by decide, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun ρ => mass ρ φ8) h
    simp only [F₃t_row, F₂t_row, Matrix.cons_val] at this
    norm_num at this
  · intro h
    have := congrArg (fun ρ => mass ρ φ8) h
    simp only [F₃t_row, Matrix.cons_val] at this
    norm_num at this
  · intro h
    have := congrArg (fun ρ => mass ρ φ8) h
    simp only [F₂t_row, Matrix.cons_val] at this
    norm_num at this

end

end Cleanroom.Corrigibility.CorrReflectFrames.Witnesses
