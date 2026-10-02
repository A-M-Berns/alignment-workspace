import Cleanroom.Info.InfoVoiLatents.Split
import Cleanroom.Info.InfoVoiLatents.VoiWitness

/-!
# info-voi-latents — the θ-hole witness (Target 4, N+)

`Λ = Unit` (the value is known: every value gauge is `0`), `θ = Fin 2` uniform, the experiment
reveals `θ` exactly, the menu is "guess `θ`, prize `M`": `voi = M/2` (`hole_voi`) while the
Λ-garbling's VOI is `voiΛ = 0` (`hole_voiΛ`), and `err = dis = 0` for every posterior over `Unit`
(`err_unit`, `dis_unit`). So the empirical part of the VOI is not bounded by any value gauge
(S3(b)); `HVal` fails here (`hole_not_hval`), as it must.

Mandate: Target 4 witness (2-070(b)).
-/

namespace Cleanroom.Info.InfoVoiLatents.Split

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Info.InfoVoiLatents.Voi

noncomputable section

/-- The θ-hole prior: `Λ = Unit`, `θ = Fin 2` uniform.
Source: [[generalization-final]] P3(b) l. 114 (`P_t(Λ = λ^H) = 1`); item 2-070(b)
Kind: D
Fidelity: exact -/
def holePrior : Unit × Fin 2 → ℝ := fun _ => 1 / 2

/-- `holePrior_mem`: supporting computation for the witnesses/plumbing of this file.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem holePrior_mem : holePrior ∈ stdSimplex ℝ (Unit × Fin 2) := by
  refine ⟨fun _ => by norm_num [holePrior], ?_⟩
  simp [holePrior, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The experiment that reveals `θ` exactly.
Source: [[generalization-final]] P3(b) l. 114 ("whenever `E_a` changes some future argmax")
Kind: D
Fidelity: exact -/
def revealθ : Experiment (Unit × Fin 2) (Fin 2) where
  k := fun p s => if s = p.2 then 1 else 0
  k_mem := fun p => ⟨fun s => by dsimp only; split_ifs <;> norm_num, by simp⟩

/-- Guess `θ`, prize `M`: `V a () ϑ = M·𝟙[a = ϑ]`.
Source: item 2-070(b)
Kind: D
Fidelity: exact -/
def holeV (M : ℝ) : Fin 2 → Unit → Fin 2 → ℝ := fun a _ ϑ => if a = ϑ then M else 0

/-- Posterior scores of the θ-hole: `postScore s a = ½ · M · 𝟙[a = s]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hole_postScore (M : ℝ) (s a : Fin 2) :
    postScore holePrior revealθ (menu (holeV M)) s a = if a = s then 1 / 2 * M else 0 := by
  unfold postScore holePrior revealθ menu holeV
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]
  fin_cases s <;> fin_cases a <;> simp [Fin.sum_univ_two]

/-- **`voi = M/2`** for the θ-hole (`0 ≤ M`).
Source: [[generalization-final]] S3(b) l. 67, P3(b) l. 114; item 2-070(b)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem hole_voi {M : ℝ} (hM : 0 ≤ M) : voi holePrior revealθ (menu (holeV M)) = M / 2 := by
  unfold voi
  rw [bayesValue_eq_sum_sup']
  simp_rw [hole_postScore M]
  have hprior : priorValue holePrior (menu (holeV M)) = M / 2 := by
    unfold priorValue
    rw [sup'_fin_two]
    simp [E, holePrior, menu, holeV, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  rw [hprior, Fin.sum_univ_two, sup'_fin_two, sup'_fin_two]
  simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, one_ne_zero,
    Fin.zero_eq_one_iff]
  rw [max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

/-- Every signal of the θ-hole has the same Λ-posterior (the point mass on `()`), so the Λ-garbling
identifies all signals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem hole_fΛ_const (s : Fin 2) : fΛ holePrior revealθ s = fΛ holePrior revealθ 0 := by
  apply Subtype.ext
  show postΛ holePrior revealθ s = postΛ holePrior revealθ 0
  have hsig : ∀ s : Fin 2, sigMass holePrior revealθ s = 1 / 2 := by
    intro s
    unfold sigMass holePrior revealθ
    simp only [Fintype.sum_prod_type, Fintype.sum_unique]
    fin_cases s <;> simp [Fin.sum_univ_two]
  have hpost : ∀ s : Fin 2, postΛ holePrior revealθ s = fun _ => 1 := by
    intro s
    funext u
    unfold postΛ post
    rw [hsig]
    unfold holePrior revealθ
    fin_cases s <;> simp [Fin.sum_univ_two]
  rw [hpost, hpost]

/-- **`voiΛ = 0`** for the θ-hole: the Λ-garbling has one effective signal, so its Bayes value is
the prior value.
Source: [[generalization-final]] S3(b) l. 67, P3(b) l. 114 (`VOI^Λ ≡ 0`)
Kind: N+
Fidelity: variant: P3(a)'s Λ-posterior garbling, which is not "informative about `Λ` only" (F12);
here both readings give `0`
Hyps: (a) all -/
theorem hole_voiΛ (M : ℝ) : voiΛ holePrior revealθ (menu (holeV M)) = 0 := by
  apply le_antisymm
  · unfold voiΛ voi
    rw [sub_nonpos]
    unfold bayesValue
    rw [Finset.sup'_le_iff]
    intro δ _
    have hk : ∀ p t, (kΛ holePrior revealθ).k p t
        = if t = fΛ holePrior revealθ 0 then 1 else 0 := by
      intro p t
      unfold kΛ pushforward
      simp only
      by_cases ht : t = fΛ holePrior revealθ 0
      · rw [if_pos ht]
        have : univ.filter (fun s => fΛ holePrior revealθ s = t) = univ := by
          ext s
          simp [hole_fΛ_const s, ht]
        rw [this]
        exact (revealθ.k_mem p).2
      · rw [if_neg ht]
        have : univ.filter (fun s => fΛ holePrior revealθ s = t) = ∅ := by
          ext s
          simp [hole_fΛ_const s, Ne.symm ht, ht]
        rw [this, Finset.sum_empty]
    simp_rw [hk, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.le_sup' (fun a => E holePrior (menu (holeV M) a)) (mem_univ _)
  · exact voi_nonneg _ _ _

/-- **`HVal` fails for the θ-hole** (the signal is about `θ`, not `Λ`), as it must for the hole
to open.
Source: [[generalization-final]] S3(c) l. 68
Kind: N+
Fidelity: exact -/
theorem hole_not_hval : ¬ HVal revealθ := by
  intro h
  have := h () 0 1 0
  simp [revealθ] at this

/-- **Every value gauge is `0` when `Λ = Unit`**: `err = 0` for any posterior in the simplex.
Source: [[generalization-final]] P3(b) l. 114 ("every value gauge at zero")
Kind: L
Fidelity: n/a -/
theorem err_unit {α : Type} {P : Unit → ℝ} (hP : P ∈ stdSimplex ℝ Unit) (Vbar : α → Unit → ℝ)
    (A : Finset α) (hA : A.Nonempty) : Coverage.err P Vbar () A hA = 0 := by
  have hP1 : P () = 1 := by
    have := hP.2
    simpa [Fintype.sum_unique] using this
  unfold Coverage.err
  rw [Finset.sup'_congr hA rfl (fun a _ => by
    show |E P (Vbar a) - Vbar a ()| = 0
    simp [E, Fintype.sum_unique, hP1])]
  exact Finset.sup'_const hA _

/-- `dis = 0` when `Λ = Unit` (the only pair is `((), ())`).
Source: [[generalization-final]] P3(b) l. 114
Kind: L
Fidelity: n/a -/
theorem dis_unit {α : Type} (P : Unit → ℝ) (η : ℝ) (Vbar : α → Unit → ℝ) (A : Finset α)
    (hA : A.Nonempty) : Coverage.dis P η Vbar A hA = 0 := by
  unfold Coverage.dis
  rw [Finset.sup'_congr hA rfl (fun a _ => ?_)]
  · exact Finset.sup'_const hA _
  · show (if h : (Coverage.effVS P η ×ˢ Coverage.effVS P η).Nonempty then
        (Coverage.effVS P η ×ˢ Coverage.effVS P η).sup' h
          (fun q => |Vbar a q.1 - Vbar a q.2|) else 0) = 0
    split_ifs with h
    · rw [Finset.sup'_congr h rfl (g := fun _ => (0 : ℝ)) (fun q _ => by simp), Finset.sup'_const]
    · rfl

end

end Cleanroom.Info.InfoVoiLatents.Split
