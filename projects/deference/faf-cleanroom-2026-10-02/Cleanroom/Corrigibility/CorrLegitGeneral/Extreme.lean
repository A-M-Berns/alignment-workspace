import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Found.LitDdbFrames.Cycle
import Cleanroom.Found.LitDdbFrames.ExamplesFact21

/-!
# corr-legit-general — T7: a single target is addressable in threshold form iff it is an
extreme candidate

A threshold event `{w : E_{P_w}(X) ≥ s}` singles out the candidate `ρ` on the support of `π`
iff `ρ` is not in the convex hull of the *other* candidates of `π` (Statement 3): strict
separation of a point from the hull of a finite set gives `(X, s)`; conversely a mixture
`ρ = ∑ λ_j ρ_j` has `E_ρ(X) ≤ max_j E_{ρ_j}(X)`, so no threshold reached by `ρ` excludes every
other candidate. Hence the threshold form says nothing about a single *interior* target.
The mandate's formula `F.candsMinus ρ` (the candidates `ρ` itself leaves open, minus `ρ`) is not
the source's set; the source and the theorem use `C_π ∖ {ρ}`.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-- A candidate `ρ` is **addressable** (in above-threshold form) if some threshold event
`[E(X) ≥ s]` coincides on `supp π` with the cell `[P = ρ]`.
Source: [[legitimacy-general-final]] Statement 3 l. 45 ("coincides on `supp P_{t₁}` with `E_Q`")
Kind: D
Fidelity: exact -/
def Addressable (F : Frame W) (π : W → ℝ) (ρ : W → ℝ) : Prop :=
  ∃ (X : W → ℝ) (s : ℝ), ∀ w ∈ supp π, (s ≤ E (F.P w) X ↔ F.P w = ρ)

/-- **Single-target addressability ⟺ extremality** (Statement 3): a candidate `ρ ∈ C_π` is
addressable iff `ρ ∉ CH(C_π ∖ {ρ})`. (⇐) Hahn–Banach separates `ρ` from the closed convex hull
of the finite set `C_π ∖ {ρ}` by a functional, which is an expectation `E_·(X)`. (⇒) if
`ρ = ∑ λ_σ σ` over the other candidates then some `σ` has `E_σ(X) ≥ E_ρ(X) ≥ s`, and the
world carrying `σ` is in the event but not in the cell.
Source: [[legitimacy-general-final]] Statement 3 l. 45, Proofs l. 95; corr-wf14b-054
Kind: P
Fidelity: exact (with `C_π ∖ {ρ}`, the source's set; see the module docstring)
Hyps: (a) `ρ ∈ F.cands π` -/
theorem addressable_iff_extreme {F : Frame W} {π ρ : W → ℝ} (hρ : ρ ∈ F.cands π) :
    Addressable F π ρ ↔ ρ ∉ convexHull ℝ (↑((F.cands π).erase ρ) : Set (W → ℝ)) := by
  constructor
  · rintro ⟨X, s, h⟩ hmem
    obtain ⟨lam, hl0, hl1, hρeq⟩ := Finset.mem_convexHull'.1 hmem
    obtain ⟨w₀, hw₀, hw₀ρ⟩ := Frame.mem_cands.1 hρ
    have hs : s ≤ E ρ X := by
      have := (h w₀ (mem_supp.2 hw₀)).2 hw₀ρ
      rwa [hw₀ρ] at this
    -- some other candidate reaches the threshold
    have hex : ∃ σ ∈ (F.cands π).erase ρ, s ≤ E σ X := by
      by_contra hnone
      have hnone : ∀ σ ∈ (F.cands π).erase ρ, E σ X < s := by
        intro σ hσ
        by_contra hc
        exact hnone ⟨σ, hσ, not_lt.1 hc⟩
      have hlt : ∑ σ ∈ (F.cands π).erase ρ, lam σ * E σ X <
          ∑ σ ∈ (F.cands π).erase ρ, lam σ * s := by
        have hpos : ∃ σ ∈ (F.cands π).erase ρ, (0 : ℝ) < lam σ := by
          have : ∑ σ ∈ (F.cands π).erase ρ, (0 : ℝ) < ∑ σ ∈ (F.cands π).erase ρ, lam σ := by
            rw [hl1, sum_const_zero]; exact one_pos
          exact exists_lt_of_sum_lt this
        obtain ⟨σ₀, hσ₀, hσ₀pos⟩ := hpos
        apply sum_lt_sum
        · intro σ hσ
          exact mul_le_mul_of_nonneg_left (hnone σ hσ).le (hl0 σ hσ)
        · exact ⟨σ₀, hσ₀, mul_lt_mul_of_pos_left (hnone σ₀ hσ₀) hσ₀pos⟩
      rw [← sum_mul, hl1, one_mul] at hlt
      have hE : E ρ X = ∑ σ ∈ (F.cands π).erase ρ, lam σ * E σ X := by
        conv_lhs => rw [← hρeq]
        rw [E_sum_left]
      linarith
    obtain ⟨σ, hσ, hσs⟩ := hex
    obtain ⟨hσne, hσc⟩ := mem_erase.1 hσ
    obtain ⟨w₁, hw₁, rfl⟩ := Frame.mem_cands.1 hσc
    exact hσne ((h w₁ (mem_supp.2 hw₁)).1 hσs)
  · intro hnot
    obtain ⟨f, u, hf, hfρ⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
      (((F.cands π).erase ρ).finite_toSet.isClosed_convexHull ℝ) hnot
    set X : W → ℝ := fun w => f (fun j => if w = j then 1 else 0) with hX
    have hfE : ∀ σ, f σ = E σ X := fun σ => StrongDual.apply_eq_E f σ
    refine ⟨X, u, fun w hw => ?_⟩
    constructor
    · intro hu
      by_contra hne
      have hmem : F.P w ∈ (F.cands π).erase ρ :=
        mem_erase.2 ⟨hne, F.P_mem_cands (mem_supp.1 hw)⟩
      have := hf _ (subset_convexHull ℝ _ (mem_coe.2 hmem))
      rw [hfE] at this
      linarith
    · intro he
      rw [he, ← hfE]
      exact hfρ.le

/-- The below-threshold form is the above-threshold form of `−X`.
Source: mandate T7 ("below-threshold by `X ↦ −X`")
Kind: L
Fidelity: n/a -/
theorem addressable_iff_le_form (F : Frame W) (π ρ : W → ℝ) :
    Addressable F π ρ ↔ ∃ (X : W → ℝ) (s : ℝ), ∀ w ∈ supp π, (E (F.P w) X ≤ s ↔ F.P w = ρ) := by
  constructor
  · rintro ⟨X, s, h⟩
    refine ⟨-X, -s, fun w hw => ?_⟩
    rw [E_neg_right, neg_le_neg_iff]
    exact h w hw
  · rintro ⟨X, s, h⟩
    refine ⟨-X, -s, fun w hw => ?_⟩
    rw [E_neg_right, neg_le_neg_iff]
    exact h w hw

/-! ## Witness B1 -/

open Cleanroom.Found.LitDdbFrames.Examples in
/-- B1's frame on three worlds: rows `(9/10, 1/10, 0)`, `(1/2, 1/2, 0)`, `(1/10, 9/10, 0)`.
Source: [[legitimacy-general-final]] Proofs l. 95 (B1)
Kind: D
Fidelity: exact -/
def ext3 : Frame (Fin 3) :=
  mk3 ![9 / 10, 1 / 10, 0] ![1 / 2, 1 / 2, 0] ![1 / 10, 9 / 10, 0]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- The uniform deferrer on three worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def third : Fin 3 → ℝ := fun _ => 1 / 3

/-- `ext3`'s rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ext3_P : ext3.P 0 = ![9 / 10, 1 / 10, 0] ∧ ext3.P 1 = ![1 / 2, 1 / 2, 0] ∧
    ext3.P 2 = ![1 / 10, 9 / 10, 0] := ⟨rfl, rfl, rfl⟩

/-- `ext3`'s rows are pairwise distinct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ext3_ne : ext3.P 0 ≠ ext3.P 1 ∧ ext3.P 0 ≠ ext3.P 2 ∧ ext3.P 1 ≠ ext3.P 2 := by
  obtain ⟨h0, h1, h2⟩ := ext3_P
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; rw [h0, h1] at this; norm_num at this
  · have := congrFun h 0; rw [h0, h2] at this; norm_num at this
  · have := congrFun h 0; rw [h1, h2] at this; norm_num at this

/-- **B1, the extreme candidates are addressable**: `X = 𝟙_{w₀}`, `s = 9/10` singles out the
first row; `X = 𝟙_{w₁}`, `s = 9/10` the third.
Source: [[legitimacy-general-final]] Proofs l. 95 (B1: "realisable singletons `{ρ₁}, {ρ₃}`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ext3_addressable_outer : Addressable ext3 third (ext3.P 0) ∧
    Addressable ext3 third (ext3.P 2) := by
  obtain ⟨h0, h1, h2⟩ := ext3_P
  obtain ⟨n01, n02, n12⟩ := ext3_ne
  constructor
  · refine ⟨ind {0}, 9 / 10, fun w _ => ?_⟩
    fin_cases w
    · show 9 / 10 ≤ E (ext3.P 0) (ind {0}) ↔ ext3.P 0 = ext3.P 0
      refine iff_of_true ?_ rfl
      rw [h0]; norm_num [E, Fin.sum_univ_three, ind, Cleanroom.Found.LitDdbFrames.Examples.vec3_two]
    · show 9 / 10 ≤ E (ext3.P 1) (ind {0}) ↔ ext3.P 1 = ext3.P 0
      refine iff_of_false ?_ n01.symm
      rw [h1]; norm_num [E, Fin.sum_univ_three, ind, Cleanroom.Found.LitDdbFrames.Examples.vec3_two]
    · show 9 / 10 ≤ E (ext3.P 2) (ind {0}) ↔ ext3.P 2 = ext3.P 0
      refine iff_of_false ?_ n02.symm
      rw [h2]; norm_num [E, Fin.sum_univ_three, ind, Cleanroom.Found.LitDdbFrames.Examples.vec3_two]
  · refine ⟨ind {1}, 9 / 10, fun w _ => ?_⟩
    fin_cases w
    · show 9 / 10 ≤ E (ext3.P 0) (ind {1}) ↔ ext3.P 0 = ext3.P 2
      refine iff_of_false ?_ n02
      rw [h0]; norm_num [E, Fin.sum_univ_three, ind, Cleanroom.Found.LitDdbFrames.Examples.vec3_two]
    · show 9 / 10 ≤ E (ext3.P 1) (ind {1}) ↔ ext3.P 1 = ext3.P 2
      refine iff_of_false ?_ n12
      rw [h1]; norm_num [E, Fin.sum_univ_three, ind, Cleanroom.Found.LitDdbFrames.Examples.vec3_two]
    · show 9 / 10 ≤ E (ext3.P 2) (ind {1}) ↔ ext3.P 2 = ext3.P 2
      refine iff_of_true ?_ rfl
      rw [h2]; norm_num [E, Fin.sum_univ_three, ind, Cleanroom.Found.LitDdbFrames.Examples.vec3_two]

/-- **B1, the middle candidate is not addressable**: `(1/2, 1/2, 0) = ½ ρ₁ + ½ ρ₃`, so for every
`X`, `E_{ρ₂}(X)` lies between `E_{ρ₁}(X)` and `E_{ρ₃}(X)` and no threshold reached by `ρ₂`
excludes both.
Source: [[legitimacy-general-final]] Proofs l. 95 (B1: "never `{ρ₂}`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ext3_not_addressable_middle : ¬ Addressable ext3 third (ext3.P 1) := by
  rintro ⟨X, s, h⟩
  obtain ⟨h0, h1, h2⟩ := ext3_P
  obtain ⟨n01, _, n12⟩ := ext3_ne
  have hsupp : ∀ w : Fin 3, w ∈ supp third := fun w => by simp [supp, third]
  have e0 := h 0 (hsupp 0)
  have e1 := h 1 (hsupp 1)
  have e2 := h 2 (hsupp 2)
  simp only [n01, n12.symm, iff_false, iff_true] at e0 e1 e2
  simp only [E, Fin.sum_univ_three, h0, h1, h2, Cleanroom.Found.LitDdbFrames.Examples.vec3_two]
    at e0 e1 e2
  norm_num at e0 e1 e2
  linarith

end

end Cleanroom.Corrigibility.CorrLegitGeneral
