import Cleanroom.Decision.DpCalibration.Defs

/-!
# Basic facts about the senses

Supporting lemmas used across the package (T1's `strictOC_calibratedState`, the uniqueness of the
strict state where `ν(O_d) > 0`, the calibrated state as a masked witness, a.s.-equal leaf sets
have equal mass, the prior-calibrated state at `⊤`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## Distributions -/

/-- Some element has positive weight. Source: none: infrastructure. Kind: L -/
theorem FinDistr.exists_pos_w' {α : Type} [Fintype α] (p : FinDistr K α) : ∃ a, 0 < p.w a := by
  by_contra h
  push Not at h
  have : ∑ a, p.w a = 0 :=
    Finset.sum_eq_zero fun a _ => le_antisymm (h a) (p.nonneg a)
  rw [p.sum_one] at this
  exact one_ne_zero this

/-- Weights of a full-support point-deviation self-model: `C[d ↦ m]` at `d` is `m`.
Source: none: infrastructure. Kind: L -/
theorem deviate_w_same (C : Proc ι acts K) (d : ι) (m : FinDistr K (acts d)) (a : acts d) :
    (C.deviate d m d).w a = m.w a := by simp

/-! ## Masses -/

/-- Leaf sets that agree on every leaf of positive mass have equal mass.
Source: [[decision-problems-v2]] Proposition 3 proof ("conditioning on equal events yields
equal conditionals")
Kind: L -/
theorem mass_congr_ae (C : Proc ι acts K) (B : Tree Ω ι acts K) {S T : Finset B.Leaves}
    (h : ∀ ℓ, 0 < leafLaw C B ℓ → (ℓ ∈ S ↔ ℓ ∈ T)) : mass C B S = mass C B T := by
  rw [mass_filter_eq C B S, mass_filter_eq C B T]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rcases (leafLaw_nonneg C B ℓ).lt_or_eq with hpos | hzero
  · simp [h ℓ hpos]
  · simp [← hzero]
where
  /-- mass as an indicator sum (local helper). -/
  mass_filter_eq (C : Proc ι acts K) (B : Tree Ω ι acts K) (S : Finset B.Leaves) :
      mass C B S = ∑ ℓ, if ℓ ∈ S then leafLaw C B ℓ else 0 := by
    unfold mass; rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Payoff sums over leaf sets that agree on every leaf of positive mass are equal.
Source: none: infrastructure
Kind: L -/
theorem paySumLeaves_congr_ae (C : Proc ι acts K) (B : Tree Ω ι acts K) {S T : Finset B.Leaves}
    (h : ∀ ℓ, 0 < leafLaw C B ℓ → (ℓ ∈ S ↔ ℓ ∈ T)) :
    ∑ ℓ ∈ S, leafLaw C B ℓ * payoff B ℓ = ∑ ℓ ∈ T, leafLaw C B ℓ * payoff B ℓ := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ℓ => 0 < leafLaw C B ℓ),
    ← Finset.sum_filter_add_sum_filter_not T (fun ℓ => 0 < leafLaw C B ℓ)]
  have hz : ∀ (U : Finset B.Leaves), ∑ ℓ ∈ U.filter (fun ℓ => ¬ 0 < leafLaw C B ℓ),
      leafLaw C B ℓ * payoff B ℓ = 0 := by
    intro U
    apply Finset.sum_eq_zero
    intro ℓ hℓ
    have := (Finset.mem_filter.mp hℓ).2
    have h0 : leafLaw C B ℓ = 0 := le_antisymm (not_lt.mp this) (leafLaw_nonneg C B ℓ)
    simp [h0]
  rw [hz S, hz T]
  congr 1
  apply Finset.sum_congr _ fun _ _ => rfl
  ext ℓ
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hS, hp⟩; exact ⟨(h ℓ hp).mp hS, hp⟩
  · rintro ⟨hT, hp⟩; exact ⟨(h ℓ hp).mpr hT, hp⟩

/-- `ν(X ∩ O) ≤ ν(O)`. Source: none: infrastructure. Kind: L -/
theorem nu_inter_le (C : Proc ι acts K) (B : Tree Ω ι acts K) (X O : Finset Ω) :
    nu C B (X ∩ O) ≤ nu C B O :=
  nu_mono C B Finset.inter_subset_right

/-- `ν(X ∩ O) = 0` when `ν(O) = 0`. Source: none: infrastructure. Kind: L -/
theorem nu_inter_eq_zero (C : Proc ι acts K) (B : Tree Ω ι acts K) {X O : Finset Ω}
    (h : nu C B O = 0) : nu C B (X ∩ O) = 0 :=
  le_antisymm (h ▸ nu_inter_le C B X O) (nu_nonneg C B _)

/-! ## The calibrated state satisfies the strict clauses (T1) -/

section calibrated

variable (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **The strictly calibrated state satisfies both clauses of Definition 8** at `d` under `C`
whenever `s_d` is `calibratedState C B (O_d)`.
Source: [[decision-problems-v2]] §3.1 Definition 8; mandate T1 (`strictOC_calibratedState`)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ν(O_d)` -/
theorem strictClausesAt_calibratedState (s : ι → State Ω K) (d : ι) (h : 0 < nu C B (obs d))
    (hs : s d = calibratedState C B (obs d) h) : StrictClausesAt s obs C B d := by
  refine ⟨fun X => ?_, fun X _ hX => ?_⟩
  · rw [hs, calibratedState_pr]
    field_simp
  · rw [hs, calibratedState_V]
    field_simp

/-- `StrictOCAt` for the calibrated state (the guard discharged by the hypothesis).
Source: mandate T1
Kind: L -/
theorem strictOCAt_calibratedState (s : ι → State Ω K) (d : ι) (h : 0 < nu C B (obs d))
    (hs : s d = calibratedState C B (obs d) h) : StrictOCAt s obs C B d :=
  fun _ => strictClausesAt_calibratedState obs C B s d h hs

/-- **The strict state is unique modulo junk** where `ν(O_d) > 0`: two states both satisfying
the strict clauses at `d` under `C` agree (`State.Agree`).
Source: [[decision-problems-v2]] Remark 4.4 ("two calibrated states sharing `O` must agree in
their `P` and `V` components"); `calibration.md` Definitions carried ("the state assignment
that makes `B` strictly observation-calibrated for `C^ε`" — unique where `ν > 0`)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ν(O_d)` -/
theorem strictClausesAt_unique (s s' : ι → State Ω K) (d : ι) (h : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (hs' : StrictClausesAt s' obs C B d) :
    State.Agree (s d) (s' d) := by
  have hP : ∀ X, (s d).pr X = (s' d).pr X := by
    intro X
    have h1 := hs.1 X
    have h2 := hs'.1 X
    have : (s d).pr X * nu C B (obs d) = (s' d).pr X * nu C B (obs d) := by rw [h1, h2]
    exact mul_right_cancel₀ h.ne' this
  refine ⟨?_, fun X hX => ?_⟩
  · apply FinDistr.ext'
    intro ω
    have := hP {ω}
    simpa [State.pr, probOf_singleton] using this
  · have hX' : 0 < (s' d).pr X := by rw [← hP X]; exact hX
    have hXO : 0 < nu C B (X ∩ obs d) := by
      have := hs.1 X
      rw [← this]
      exact mul_pos hX h
    have h1 := hs.2 X hX hXO
    have h2 := hs'.2 X hX' hXO
    have : (s d).V X * nu C B (X ∩ obs d) = (s' d).V X * nu C B (X ∩ obs d) := by rw [h1, h2]
    exact mul_right_cancel₀ hXO.ne' this

/-- **The calibrated state of a full-support local self-model is a masked witness**: if
`m` is full-support, `0 < ν_{C[d↦m]}(O_d)` and `s_d = calibratedState (C[d↦m]) B O_d`, then
`MaskedOCAt s obs C B d` (LF, vacuity; the first disjunct, so the reading is irrelevant).
Source: [[decision-problems-v2]] §3.1 Definition 9
Kind: L
Fidelity: variant: null case read as vacuity (A5) — not exercised here (first disjunct) -/
theorem maskedOCAt_calibratedState (s : ι → State Ω K) (d : ι) (m : FinDistr K (acts d))
    (hm : ∀ a, 0 < m.w a) (h : 0 < nu (C.deviate d m) B (obs d))
    (hs : s d = calibratedState (C.deviate d m) B (obs d) h) :
    MaskedOCAt s obs C B d :=
  Or.inl ⟨C.deviate d m, ⟨m, hm, rfl⟩, h, strictClausesAt_calibratedState obs _ B s d h hs⟩

/-- The same for the `LP` (plain) variant: any local self-model realizing `O_d`.
Source: [[decision-problems-v2]] Appendix B ("plain")
Kind: L -/
theorem maskedOCAtV_LP_calibratedState (s : ι → State Ω K) (d : ι) (m : FinDistr K (acts d))
    (h : 0 < nu (C.deviate d m) B (obs d))
    (hs : s d = calibratedState (C.deviate d m) B (obs d) h) (r : NullReading) :
    MaskedOCAtV s obs C B .LP r d :=
  Or.inl ⟨C.deviate d m, ⟨m, rfl⟩, h, strictClausesAt_calibratedState obs _ B s d h hs⟩

/-- **The calibrated state at `⊤` is prior-calibrated** (Definition 11): `P = ν`,
`V(X) = 𝔼[r | λ ⊨ X]` on `ν`-non-null `X`.
Source: [[decision-problems-v2]] §3.1 Definition 11
Kind: L -/
theorem priorCalibrated_calibratedState_univ (h : 0 < nu C B Finset.univ) :
    PriorCalibrated C B (calibratedState C B Finset.univ h) := by
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · rw [calibratedState_pr, Finset.inter_univ, nu_univ]; simp
  · rw [calibratedState_V, Finset.inter_univ]
    field_simp

/-- `ν(⊤) = 1 > 0`. Source: none: infrastructure. Kind: L -/
theorem nu_univ_pos : 0 < nu C B Finset.univ := by rw [nu_univ]; exact one_pos

end calibrated

end Cleanroom.Decision.DpCalibration
