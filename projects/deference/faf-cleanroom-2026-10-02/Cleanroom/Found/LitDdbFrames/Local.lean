import Cleanroom.Found.LitDdbFrames.Defs

/-!
# Local (question-relative) deference — definitions only

Package `lit-ddb-frames`, Target 6 (item 072's definitional half). A question is a map
`Q : W → C` whose cells are its fibres; a partial answer is a preimage `Q ⁻¹' T`. The theorem
"local Total Trust for all 2-cell questions ⟺ Simple Trust", fn 66's witness and the open
direction of fn 65 are `corr-legit-general`'s and are not stated here.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-- A random variable `X` is *determined by the answer to `Q`* (measurable with respect to the
partition of `Q`): constant on each fibre of `Q`.
Source: [[Deference Done Better]] §5 l. 396, fn 63 l. 1233
Kind: D
Fidelity: exact -/
def MeasurableWrt (Q : W → C) (X : W → ℝ) : Prop := ∀ w v, Q w = Q v → X w = X v

/-- A *partial answer* to `Q`: the union of the cells in `T`, i.e. `Q ⁻¹' T` as a `Finset W`.
Source: [[Deference Done Better]] §5 l. 396, fn 62 l. 1231
Kind: D
Fidelity: exact -/
def answer (Q : W → C) (T : Finset C) : Finset W := univ.filter (fun w => Q w ∈ T)

/-- **Reflection with respect to `Q`**: for every candidate `ρ ∈ C_π` and partial answer `q`,
`π(q | P = ρ) = ρ(q)`, in product form `π(q ∧ [P = ρ]) = π(P = ρ) · ρ(q)`.
Source: [[Deference Done Better]] §5 l. 396, fn 62 l. 1231
Kind: D
Fidelity: exact -/
def ReflectsWrt (Q : W → C) (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ ρ ∈ F.cands π, ∀ T : Finset C,
    mass π (F.cell ρ ∩ answer Q T) = mass π (F.cell ρ) * mass ρ (answer Q T)

/-- **Total Trust with respect to `Q`**: the product form of Total Trust, for every `Q`-measurable
random variable `X` and every threshold.
Source: [[Deference Done Better]] §5 l. 396, fn 63 l. 1233
Kind: D
Fidelity: exact -/
def TotalTrustWrt (Q : W → C) (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ X : W → ℝ, MeasurableWrt Q X →
    ∀ s : ℝ, 0 ≤ ∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0)

/-- **Value with respect to `Q`**: Value over nonempty menus of `Q`-measurable options; strategies
are still cellwise in `P` (the expert decides, the utilities are `Q`-determined).
Source: [[Deference Done Better]] §5 l. 396, fn 64 l. 1235
Kind: D
Fidelity: exact -/
def ValuesWrt (Q : W → C) (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ 𝒪 : DecisionProblem W, 𝒪.Nonempty → (∀ o ∈ 𝒪, MeasurableWrt Q o) →
    ∀ S, F.Recommended 𝒪 S → ∀ o ∈ 𝒪, E π o ≤ stratValue π S

/-- Every random variable is measurable with respect to the identity question.
Source: none: infrastructure (Target 6)
Kind: L
Fidelity: n/a -/
theorem measurableWrt_id (X : W → ℝ) : MeasurableWrt (id : W → W) X :=
  fun _ _ h => by simp only [id] at h; rw [h]

/-- Total Trust is Total Trust with respect to the finest question `id`.
Source: none: infrastructure (Target 6)
Kind: L
Fidelity: n/a -/
theorem totalTrust_iff_totalTrustWrt_id {π : W → ℝ} {F : Frame W} :
    TotalTrust π F ↔ TotalTrustWrt (id : W → W) π F :=
  ⟨fun h X _ s => h X s, fun h X s => h X (measurableWrt_id X) s⟩

/-- Total Trust implies Total Trust with respect to every question.
Source: none: infrastructure (Target 6)
Kind: L
Fidelity: n/a -/
theorem TotalTrust.wrt {π : W → ℝ} {F : Frame W} (h : TotalTrust π F) (Q : W → C) :
    TotalTrustWrt Q π F :=
  fun X _ s => h X s

/-- Value implies Value with respect to every question.
Source: none: infrastructure (Target 6)
Kind: L
Fidelity: n/a -/
theorem Value.wrt {π : W → ℝ} {F : Frame W} (h : Value π F) (Q : W → C) : ValuesWrt Q π F :=
  fun 𝒪 hne _ S hS o ho => h 𝒪 hne S hS o ho

/-- The 2-cell question `{q, ¬q}` of a proposition, as the map `w ↦ decide (w ∈ q) : W → Bool`.
Source: [[Deference Done Better]] §5 l. 398
Kind: D
Fidelity: exact -/
def questionOf (q : Finset W) : W → Bool := fun w => decide (w ∈ q)

/-- The indicator of `q` is measurable with respect to the 2-cell question of `q`.
Source: none: infrastructure (Target 6)
Kind: L
Fidelity: n/a -/
theorem measurableWrt_questionOf_ind (q : Finset W) : MeasurableWrt (questionOf q) (ind q) := by
  intro w v h
  simp only [questionOf, decide_eq_decide] at h
  simp [ind, h]

end

end Cleanroom.Found.LitDdbFrames
