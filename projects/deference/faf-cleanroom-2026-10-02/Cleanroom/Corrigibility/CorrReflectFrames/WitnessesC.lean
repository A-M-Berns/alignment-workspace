import Cleanroom.Corrigibility.CorrReflectFrames.Selection
import Mathlib.Data.Fin.VecNotation

/-!
# corr-reflect-frames — witnesses C (selection)

* **Adapted stopping retains its grounds** (`retainsGrounds_of_adapted`): a stopping rule whose
  event `{τ = m}` is `ℱ_m`-measurable is, by that very condition, a retention-of-grounds
  selection — the two definitions coincide (kind L), so adapted optional stopping preserves
  reflection by the selection theorem. Instance: the depth-3 coin tree
  `W = Θ × {0,1}³`, `Θ = {1/3, 2/3}` uniform, i.i.d. flips, with the non-trivial rule "stop after
  one flip if it is heads, else after three"; reflective by `selectFrame_reflects` with no
  enumeration. No atom of the tree is `π`-null (all weights are products of positive rationals).
* **The forgetting rule** (`selection_checks.py` C1, radical/selection R2.2(i)): six worlds,
  `π = (1,2,3,1,2,3)/12`, `ℱ₁ = {1}{2,3}{4}{5,6}`, `ℱ₃ = {1,2,3}{4,5,6}`, world 4 routed to `ℱ₃`,
  every other world to `ℱ₁`: retention fails (world 5 is `ℱ₃`-indistinguishable from world 4 but
  selects `ℱ₁`), the selected frame is not estimate-matching (`πP ≠ π` at world 4:
  `1/72 ≠ 1/12`), hence not reflected. No atom is `π`-null.
* Not built (budget): the path-maximum refutation (`353/540`), Sel.2's face-value adoption
  (`8/13`), the kernel-change frame (C4), the both-zero builder (`1/325`).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

/-! ## Adapted stopping -/

/-- **Adapted stopping rules retain their grounds.** With candidates `f m := σ(first m flips)` and
a rule `τ`, "`{τ = m}` is `ℱ_m`-measurable" (`∀ m w w', τ w = m → f m w = f m w' → τ w' = m`) is
literally `RetainsGrounds f τ`: the per-`k` retention hypothesis of the selection theorem is the
adaptedness condition of optional stopping. (Why R1.1's common-`G` hypothesis does not cover
stopping: findings F2.)
Source: [[selection]] R1.3 l. 31; [[radical]] Sel.1 l. 342; [[armstrong]] A1 (optional stopping
does not break SU)
Kind: L
Fidelity: exact (the identity of the two conditions)
Hyps: (a) none -/
theorem retainsGrounds_of_adapted {W S K : Type} (f : K → W → S) (τ : W → K)
    (h : ∀ m w w', τ w = m → f m w = f m w' → τ w' = m) : RetainsGrounds f τ := h

/-- The depth-3 coin tree: a world is `(θ, x₁, x₂, x₃)` with `θ ∈ {1/3, 2/3}` (`0 ↦ 1/3`,
`1 ↦ 2/3`) and three flips.
Source: [[radical]] `s3`; [[selection]] R1.3
Kind: D
Fidelity: exact -/
abbrev Tree := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- The prior on the tree: `θ` uniform, flips i.i.d. with `P(heads | θ) = 1/3` or `2/3`.
Source: [[radical]] `s3`
Kind: D
Fidelity: exact -/
def πTree : Tree → ℝ := fun w =>
  (1 / 2) * (if w.2.1 = w.1 then 2 / 3 else 1 / 3) * (if w.2.2.1 = w.1 then 2 / 3 else 1 / 3) *
    (if w.2.2.2 = w.1 then 2 / 3 else 1 / 3)

/-- The tree prior is nonnegative (every atom is positive: no null cells).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πTree_pos (w : Tree) : 0 < πTree w := by
  unfold πTree; split_ifs <;> norm_num

/-- The filtration: `f m w` records the first `m` flips (masking the rest with `0`).
Source: [[radical]] `s3` (`ℱ_m = σ(first m flips)`)
Kind: D
Fidelity: exact (as a partition map) -/
def flips : Fin 4 → Tree → Fin 2 × Fin 2 × Fin 2 :=
  ![fun _ => (0, 0, 0), fun w => (w.2.1, 0, 0), fun w => (w.2.1, w.2.2.1, 0),
    fun w => (w.2.1, w.2.2.1, w.2.2.2)]

/-- A non-trivial adapted rule: stop after one flip if it is heads, else after all three.
Source: [[radical]] `s3` (one of the 26 adapted rules)
Kind: D
Fidelity: exact -/
def τ₁₃ : Tree → Fin 4 := fun w => if w.2.1 = 1 then 1 else 3

/-- The rule `τ₁₃` is adapted, hence retains its grounds.
Source: [[radical]] Sel.1 l. 342
Kind: L
Fidelity: n/a -/
theorem τ₁₃_retains : RetainsGrounds flips τ₁₃ := by
  apply retainsGrounds_of_adapted
  intro m w w' hw hf
  simp only [τ₁₃] at hw ⊢
  split_ifs at hw with h1
  · subst hw
    simp only [flips, Matrix.cons_val, Prod.mk.injEq] at hf
    rw [if_pos (hf.1 ▸ h1)]
  · subst hw
    simp only [flips, Matrix.cons_val, Prod.mk.injEq] at hf
    rw [if_neg (hf.1 ▸ h1)]

/-- **Adapted optional stopping preserves reflection** (N+ instance): the stopped frame of the
rule `τ₁₃` on the coin tree is reflected by the prior, value-reflective and estimate-matching —
by the selection theorem, with no enumeration of the sixteen atoms.
Source: [[radical]] Sel.1 l. 342; [[selection]] R1.3 l. 31; [[armstrong]] A1 l. 262
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem stopped_frame_reflects :
    Reflects πTree (selectFrame πTree (fun w => (πTree_pos w).le) flips τ₁₃) ∧
      ValueReflects πTree (selectFrame πTree (fun w => (πTree_pos w).le) flips τ₁₃) ∧
      EstimateMatching πTree (selectFrame πTree (fun w => (πTree_pos w).le) flips τ₁₃) :=
  ⟨selectFrame_reflects _ τ₁₃_retains, selectFrame_valueReflects _ τ₁₃_retains,
    selectFrame_estimateMatching _ τ₁₃_retains⟩

/-! ## The forgetting rule (six worlds) -/

/-- The six-world prior `(1,2,3,1,2,3)/12`.
Source: [[selection]] `selection_checks.py` C1; [[armstrong]] A1 (iii)
Kind: D
Fidelity: exact -/
def π6w : Fin 6 → ℝ := ![1 / 12, 2 / 12, 3 / 12, 1 / 12, 2 / 12, 3 / 12]

/-- `π6w` is nonnegative (all atoms positive).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π6w_nonneg (w : Fin 6) : 0 ≤ π6w w := by fin_cases w <;> norm_num [π6w]

/-- `ℱ₁ = {1}{2,3}{4}{5,6}` as a partition map.
Source: [[selection]] `selection_checks.py` C1
Kind: D
Fidelity: exact -/
def f₁ : Fin 6 → Fin 4 := ![0, 1, 1, 2, 3, 3]

/-- `ℱ₃ = {1,2,3}{4,5,6}` as a partition map.
Source: [[selection]] `selection_checks.py` C1
Kind: D
Fidelity: exact -/
def f₃ : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 1]

/-- The two candidates, indexed by `Bool`: `false ↦ ℱ₁`, `true ↦ ℱ₃`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def fK : Bool → Fin 6 → Fin 4 := fun b => if b then f₃ else f₁

/-- The forgetting rule: world `4` (index `3`) is routed to the coarse `ℱ₃`, every other world to
`ℱ₁`.
Source: [[selection]] `selection_checks.py` C1 (`rule = (0,0,0,2,0,0)`)
Kind: D
Fidelity: exact -/
def sForget : Fin 6 → Bool := fun w => decide (w = 3)

/-- **The forgetting rule does not retain its grounds**: world `5` (index `4`) is
`ℱ₃`-indistinguishable from world `4` but selects `ℱ₁`.
Source: [[selection]] R2.2(i) l. 51 (forgetting); `selection_checks.py` C1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sForget_not_retains : ¬ RetainsGrounds fK sForget := by
  intro h
  have := h true 3 4 (by simp [sForget]) (by simp [fK, f₃])
  simp [sForget] at this

/-- The mass of the `ℱ₃`-fibre of world `3` is `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_f₃_3 : mass π6w (fibre f₃ 3) = 1 / 2 := by
  rw [mass, fibre, sum_filter]
  simp [Fin.sum_univ_succ, f₃, π6w]
  norm_num

/-- **The forgetting rule's frame is not estimate-matching**: stationarity fails at world `4`
(index `3`): `∑ w, π w · P_w(3) = π(3) · (1/6) = 1/72 ≠ 1/12`. Hence, by
`varReflects_of_reflects` and `estimateMatching_of_varReflects`, it is not reflected either:
the retention hypothesis of the selection theorem is the content.
Source: [[selection]] R1.1 l. 27 ("the forgetting rule … fails all three tests"), R2.2(i);
`selection_checks.py` C1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sForget_not_estimateMatching :
    ¬ EstimateMatching π6w (selectFrame π6w π6w_nonneg fK sForget) := by
  rw [estimateMatching_iff_stationary]
  intro h
  have h3 := h 3
  have hoff : ∀ w : Fin 6, w ≠ 3 → (selectFrame π6w π6w_nonneg fK sForget).P w 3 = 0 := by
    intro w hw
    show condRow π6w (fK (sForget w)) w 3 = 0
    have hs : sForget w = false := by simp [sForget, hw]
    rw [hs]
    simp only [fK, Bool.false_eq_true, if_false]
    unfold condRow
    split_ifs with hpos
    · have : (3 : Fin 6) ∉ fibre f₁ w := by
        rw [mem_fibre]; fin_cases w <;> simp_all [f₁]
      simp [ind, this]
    · simp [hw.symm]
  have hon : (selectFrame π6w π6w_nonneg fK sForget).P 3 3 = 1 / 6 := by
    show condRow π6w (fK (sForget 3)) 3 3 = 1 / 6
    have hs : sForget 3 = true := by simp [sForget]
    rw [hs]
    simp only [fK, if_true]
    have hpos : 0 < mass π6w (fibre f₃ 3) := by rw [mass_fibre_f₃_3]; norm_num
    rw [condRow_apply_of_pos hpos, mass_fibre_f₃_3]
    simp [ind, mem_fibre_self, π6w] <;> norm_num
  rw [Fin.sum_univ_six] at h3
  rw [hoff 0 (by decide), hoff 1 (by decide), hoff 2 (by decide), hon, hoff 4 (by decide),
    hoff 5 (by decide)] at h3
  simp [π6w] at h3 <;> norm_num at h3

/-- **The forgetting rule's frame is not reflected.**
Source: [[selection]] R1.1 l. 27; R2.2(i)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sForget_not_reflects : ¬ Reflects π6w (selectFrame π6w π6w_nonneg fK sForget) :=
  fun h => sForget_not_estimateMatching
    (estimateMatching_of_varReflects (varReflects_of_reflects π6w_nonneg h))

end

end Cleanroom.Corrigibility.CorrReflectFrames.Witnesses
