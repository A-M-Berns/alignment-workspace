import Cleanroom.Corrigibility.CorrLegitGeneral.Defs

/-!
# corr-legit-general — the vacuity traps, made explicit

The mandate's two traps (Known issues 1) and a third found by the round-1 adversarial audit
(N1, N2), adopted from its probe `Vacuity.lean`:

1. `L = ∅`: `legitTotalTrustWrt_empty` (Defs) — hence `0 < mass π L` on every conditioned
   headline.
2. **A one-cell question** makes every `Q`-measurable variable constant, so every nonnegative
   deferrer totally trusts every frame with respect to it (`totalTrustWrt_const_question`), and
   the criterion of record with a one-cell `Q` says nothing for any `L`
   (`legitTotalTrustWrt_const_question`). Every local witness in this package therefore shows
   two positive-mass cells (`leak4_guards`, `fn66`, `tie4`, `cF2`, `tieF`, `p2_instance`).
3. **The Dirac frame** (the expert at `w` is certain of `w`) is totally trusted by every
   nonnegative deferrer, hence `LegitimizingTT π (diracFrame W) L` holds for every `π ≥ 0` and
   every `L`: the step-two hypothesis of the composition theorems is trivially inhabited by
   `F₃ := diracFrame W`. The non-degenerate positive instance of `compose_global` is
   `WitnessesCompose.lean`'s `compose_positive_instance`.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **The one-cell trap**: with respect to a one-cell question every nonnegative deferrer totally
trusts every frame, because every `Q`-measurable variable is constant and the threshold
inequality at a constant `X ≡ c` reads `(c − s)·𝟙[s ≤ c]·π(W) ≥ 0`.
Source: mandate Known issues 1 (second trap); audit r1 adversarial N1
Kind: N-
Fidelity: n/a (the degenerate instance the local witnesses must avoid)
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem totalTrustWrt_const_question (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (F : Frame W) :
    TotalTrustWrt (fun _ => ()) π F := by
  intro X hX s
  apply sum_nonneg
  intro w _
  have hXw : ∀ v, X v = X w := fun v => hX v w rfl
  have hE : E (F.P w) X = X w := by
    have : X = fun _ => X w := funext hXw
    rw [this]; exact E_const (F.P_mem w) (X w)
  rw [hE]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (hπ w) (by linarith)) zero_le_one
  · simp

/-- The criterion of record with a one-cell question holds for every `L`: the second reason every
local headline's witness carries two positive-mass cells.
Source: mandate Known issues 1 (second trap); audit r1 adversarial N1
Kind: N-
Fidelity: n/a
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem legitTotalTrustWrt_const_question (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (F : Frame W)
    (L : Finset W) : LegitTotalTrustWrt (fun _ => ()) π F L :=
  totalTrustWrt_const_question _ (restrict_nonneg hπ L) F

/-- The Dirac frame: the expert at `w` is certain of `w`.
Source: audit r1 adversarial N2 (probe `Vacuity.lean`)
Kind: D
Fidelity: n/a -/
def diracFrame (W : Type) [Fintype W] [DecidableEq W] : Frame W where
  P := fun w => ind {w}
  P_mem := fun w => ⟨fun v => by unfold ind; split_ifs <;> norm_num, by simp [ind]⟩

/-- Every nonnegative deferrer totally trusts the Dirac frame (`E_{δ_w} X = X w`, so the
threshold inequality is termwise `π w · (X w − s) · 𝟙[s ≤ X w] ≥ 0`).
Source: audit r1 adversarial N2
Kind: N-
Fidelity: n/a
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem totalTrust_diracFrame (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) : TotalTrust π (diracFrame W) := by
  intro X s
  apply sum_nonneg
  intro w _
  have hE : E ((diracFrame W).P w) X = X w := by
    simp [diracFrame, E, ind]
  rw [hE]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (hπ w) (by linarith)) zero_le_one
  · simp

/-- `L`-conditioned Total Trust toward the Dirac frame holds for every `π ≥ 0` and every `L`: the
step-two hypothesis of `compose_global`/`compose_local_of_mixture` is inhabited for free by
`F₃ := diracFrame W`, which is why the composition rows cite a non-Dirac positive instance.
Source: audit r1 adversarial N2
Kind: N-
Fidelity: n/a
Hyps: (a) `∀ w, 0 ≤ π w` -/
theorem legitimizingTT_diracFrame (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (L : Finset W) :
    LegitimizingTT π (diracFrame W) L :=
  totalTrust_diracFrame _ (restrict_nonneg hπ L)

end

end Cleanroom.Corrigibility.CorrLegitGeneral
