import Cleanroom.Fixpoint.FixOraclesCorresp.BrouwerOnly

/-!
# Audit round 3 (adversarial) probe: Nash's map is also an exact reformulation

Not imported by the library. `reflective_of_nashStep_eq` gives one direction (a fixed point of
`nashStep u` in the cube is reflective for `evOf u` at `1/2`). Adversarial question: is the converse
true — i.e. is `nashStep u`'s fixed-point set in the cube *exactly* the reflective set (= the Nash
set by Theorem 4.1), the way `clampStep_eq_iff_reflective` shows for the clamp step? If so, the
"two independent proofs" are Brouwer applied to two different self-maps of the cube with the *same*
fixed-point set, and the independence is a fact about the maps (and proof terms), not about the
fixed points found. Answer: yes.
-/

namespace AdvNashStepIffProbe

open Cleanroom.Fixpoint.FixOraclesCorresp Set StrategicGame

/-- A reflective vector is a fixed point of Nash's map — on or off the cube (the elaborator's
unused-variable lint showed the cube hypothesis is not needed: reflectivity pins `x i` to `1`, `0`,
or leaves `gain = 0`, and in each case the map is the identity at `i`). -/
theorem nashStep_eq_of_reflective {N : Type*} [Fintype N] [DecidableEq N]
    {u : (N → Fin 2) → N → ℝ} {x : N → ℝ}
    (h : Reflective (evOf u) (fun _ => 1 / 2) x) : nashStep u x = x := by
  funext i
  have hi := h i
  simp only [evOf] at hi
  simp only [nashStep]
  rcases lt_trichotomy (gain u i x) 0 with hneg | hzero | hpos
  · have h0 : x i = 0 := hi.2 (by linarith)
    have hA : max 0 ((1 - x i) * gain u i x) = 0 :=
      max_eq_left (by rw [h0, sub_zero, one_mul]; exact hneg.le)
    have hB : max 0 (-(x i) * gain u i x) = 0 :=
      max_eq_left (by rw [h0]; simp)
    rw [hA, hB, h0]
    norm_num
  · have hA : max 0 ((1 - x i) * gain u i x) = 0 := by rw [hzero]; simp
    have hB : max 0 (-(x i) * gain u i x) = 0 := by rw [hzero]; simp
    rw [hA, hB]
    ring
  · have h1 : x i = 1 := hi.1 (by linarith)
    have hA : max 0 ((1 - x i) * gain u i x) = 0 := by rw [h1]; simp
    have hB : max 0 (-(x i) * gain u i x) = 0 :=
      max_eq_left (by rw [h1]; linarith)
    rw [hA, hB, h1]
    norm_num

/-- On the cube, the fixed points of Nash's map are exactly the reflective vectors. -/
theorem nashStep_eq_iff_reflective {N : Type*} [Fintype N] [DecidableEq N]
    {u : (N → Fin 2) → N → ℝ} {x : N → ℝ} (hx : x ∈ cube N) :
    nashStep u x = x ↔ Reflective (evOf u) (fun _ => 1 / 2) x :=
  ⟨reflective_of_nashStep_eq hx, nashStep_eq_of_reflective⟩

/-- Hence the clamp step and Nash's map have the same fixed points in the cube: the two Brouwer
routes are Brouwer on two different maps with one fixed-point set. -/
theorem clampStep_eq_iff_nashStep_eq {N : Type*} [Fintype N] [DecidableEq N]
    {u : (N → Fin 2) → N → ℝ} {x : N → ℝ} (hx : x ∈ cube N) :
    clampStep (evOf u) (fun _ => 1 / 2) x = x ↔ nashStep u x = x := by
  rw [clampStep_eq_iff_reflective hx, nashStep_eq_iff_reflective hx]

/-- And both are the Nash set: `σ` is an EconCSLib mixed Nash equilibrium iff its answer vector is a
fixed point of Nash's map. -/
theorem isMixedNashEq_iff_nashStep_eq {N : Type*} [Fintype N] [DecidableEq N]
    (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u)) :
    IsMixedNashEq (twoActionGame u) σ ↔ nashStep u (toCube σ) = toCube σ := by
  rw [isMixedNashEq_iff_reflective, nashStep_eq_iff_reflective (toCube_mem_cube σ)]

end AdvNashStepIffProbe
