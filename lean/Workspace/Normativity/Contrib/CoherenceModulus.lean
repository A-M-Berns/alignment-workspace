/-
# From row conformance to a coherence measure

Per-row conformance is presentation-relative: `g_j(p) ≤ δ` on every displayed row
says nothing on its own about how far `p` is from the region.  What converts it
into a measure is the **support-function presentation over a net**, and this file
proves the conversion with its constants.

For a finite set of worlds `W` and a coefficient vector `c`, the *support gap*

    gap(c)  =  min over w in W of ⟪c, w⟫  −  ⟪c, p⟫

is nonpositive exactly when `p` respects the half-space `c` cuts from `conv W`.
Ranging `c` over the unit `ℓ¹` ball, `sup_c gap(c)⁺` is the `ℓ^∞` distance from `p`
to `conv W` — that is ordinary convex duality, cited here and not reproved.  What
*is* proved here is the finite-net modulus:

    conformance `δ` on an `ℓ¹`-net of mesh `m`  ⟹  gap(c) ≤ δ + m  for every `c`,

with the Hölder step that supplies the constant.  The Lipschitz factor is
`max over w of ‖w − p‖_∞`, which is at most `1` on the price cube, so the modulus
is `δ + m` and not `δ + 2m`.

The negative half — that an arbitrary presentation of the same region gives no
distance bound at all — is a witness in the round's
`tests/test_deduction.py::PresentationRelativeConformance`, not a theorem here.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.TraderizedEnforcement

namespace Workspace.Normativity.Contrib.CoherenceModulus

open Finset
open Workspace.Normativity.Contrib.TraderizedEnforcement

variable {κ ι : Type*} [DecidableEq κ]

/-- The `ℓ¹` mass of a coefficient vector over the priced coordinates. -/
def l1 (coords : Finset κ) (u : κ → ℚ) : ℚ := ∑ k ∈ coords, |u k|

theorem l1_nonneg (coords : Finset κ) (u : κ → ℚ) : 0 ≤ l1 coords u :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Hölder, in the only form used: an `ℓ¹` coefficient vector against a uniformly
bounded displacement. -/
theorem abs_pair_le_l1_mul (coords : Finset κ) (u y : κ → ℚ) {B : ℚ} (hB : 0 ≤ B)
    (hy : ∀ k ∈ coords, |y k| ≤ B) :
    |pair coords u y| ≤ l1 coords u * B := by
  unfold pair l1
  calc |∑ k ∈ coords, u k * y k|
      ≤ ∑ k ∈ coords, |u k * y k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ coords, |u k| * |y k| := by
        exact Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ k ∈ coords, |u k| * B :=
        Finset.sum_le_sum fun k hk =>
          mul_le_mul_of_nonneg_left (hy k hk) (abs_nonneg _)
    _ = (∑ k ∈ coords, |u k|) * B := by rw [Finset.sum_mul]

/-- The support gap of a coefficient vector at a displayed price, relative to a
supplied lower envelope `low`. -/
def gap (coords : Finset κ) (low : (κ → ℚ) → ℚ) (p : κ → ℚ) (c : κ → ℚ) : ℚ :=
  low c - pair coords c p

/-- **The net modulus.**  If the displayed price conforms to the support-function
row of `c'` within `δ`, and `c` is within `ℓ¹`-distance `mesh` of `c'`, then the
support gap of `c` is at most `δ + mesh` — provided every world's displacement from
the price is bounded by `1`, which it is on the price cube.

`low` is any lower envelope of the worlds' pairings that is attained: the minimum
over a nonempty finite world set. -/
theorem gap_le_of_net (coords : Finset κ) (worlds : Finset ι) (Wld : ι → κ → ℚ)
    (p : κ → ℚ) (low : (κ → ℚ) → ℚ)
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w))
    (hlow_att : ∀ c, ∃ w ∈ worlds, low c = pair coords c (Wld w))
    (hcube : ∀ w ∈ worlds, ∀ k ∈ coords, |Wld w k - p k| ≤ 1)
    {δ mesh : ℚ} (hmesh : 0 ≤ mesh) (c c' : κ → ℚ)
    (hnet : l1 coords (fun k => c k - c' k) ≤ mesh)
    (hconf : gap coords low p c' ≤ δ) :
    gap coords low p c ≤ δ + mesh := by
  obtain ⟨w₀, hw₀, hlow'⟩ := hlow_att c'
  have hsplit : pair coords c (fun k => Wld w₀ k - p k) =
      pair coords c' (fun k => Wld w₀ k - p k) +
        pair coords (fun k => c k - c' k) (fun k => Wld w₀ k - p k) := by
    rw [← pair_add_left]
    unfold pair
    exact Finset.sum_congr rfl fun k _ => by ring
  have hHolder : |pair coords (fun k => c k - c' k) (fun k => Wld w₀ k - p k)|
      ≤ l1 coords (fun k => c k - c' k) * 1 :=
    abs_pair_le_l1_mul coords _ _ zero_le_one (fun k hk => hcube w₀ hw₀ k hk)
  have hres : pair coords (fun k => c k - c' k) (fun k => Wld w₀ k - p k) ≤ mesh := by
    have := (abs_le.mp hHolder).2
    rw [mul_one] at this
    exact this.trans hnet
  have hc' : pair coords c' (fun k => Wld w₀ k - p k) ≤ δ := by
    rw [pair_sub, ← hlow']
    exact hconf
  have hgapc : gap coords low p c ≤ pair coords c (fun k => Wld w₀ k - p k) := by
    rw [pair_sub, gap]
    have := hlow_le c w₀ hw₀
    linarith
  rw [hsplit] at hgapc
  linarith

/-- **Every coefficient vector at once.**  Conformance on a net bounds the support
gap uniformly over the unit `ℓ¹` ball, which is the quantity ordinary duality
identifies with the `ℓ^∞` distance to `conv W`. -/
theorem gap_le_of_net_cover (coords : Finset κ) (worlds : Finset ι)
    (Wld : ι → κ → ℚ) (p : κ → ℚ) (low : (κ → ℚ) → ℚ) (net : Finset (κ → ℚ))
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w))
    (hlow_att : ∀ c, ∃ w ∈ worlds, low c = pair coords c (Wld w))
    (hcube : ∀ w ∈ worlds, ∀ k ∈ coords, |Wld w k - p k| ≤ 1)
    {δ mesh : ℚ} (hmesh : 0 ≤ mesh)
    (hconf : ∀ c' ∈ net, gap coords low p c' ≤ δ)
    (hcover : ∀ c : κ → ℚ, l1 coords c ≤ 1 →
      ∃ c' ∈ net, l1 coords (fun k => c k - c' k) ≤ mesh) :
    ∀ c : κ → ℚ, l1 coords c ≤ 1 → gap coords low p c ≤ δ + mesh := by
  intro c hc
  obtain ⟨c', hc'net, hc'close⟩ := hcover c hc
  exact gap_le_of_net coords worlds Wld p low hlow_le hlow_att hcube hmesh c c'
    hc'close (hconf c' hc'net)

/-- The gap vanishes on the worlds themselves, which is the world-inclusivity of a
support-function presentation: reading each row's right-hand side off the worlds
makes every world satisfy every row. -/
theorem gap_nonpos_at_world (coords : Finset κ) (worlds : Finset ι)
    (Wld : ι → κ → ℚ) (low : (κ → ℚ) → ℚ)
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w))
    (c : κ → ℚ) {w : ι} (hw : w ∈ worlds) :
    gap coords low (Wld w) c ≤ 0 := by
  unfold gap
  have := hlow_le c w hw
  linarith

/-- Inhabitation: one priced coordinate, the single world `0`, the displayed price
`1/4`.  The coefficient `-1` has support gap `1/4` — which is exactly the `ℓ^∞`
distance from `1/4` to `{0}` — the net member `-3/4` conforms at `3/16`, and the
two are `1/4` apart in `ℓ¹`, so the modulus `3/16 + 1/4` holds with room. -/
theorem net_modulus_is_nonvacuous :
    ∃ (coords : Finset ℕ) (worlds : Finset ℕ) (Wld : ℕ → ℕ → ℚ) (p : ℕ → ℚ)
      (low : (ℕ → ℚ) → ℚ) (c c' : ℕ → ℚ),
      (∀ c₀, ∀ w ∈ worlds, low c₀ ≤ pair coords c₀ (Wld w)) ∧
      (∀ c₀, ∃ w ∈ worlds, low c₀ = pair coords c₀ (Wld w)) ∧
      (∀ w ∈ worlds, ∀ k ∈ coords, |Wld w k - p k| ≤ 1) ∧
      l1 coords (fun k => c k - c' k) = 1 / 4 ∧
      gap coords low p c' = 3 / 16 ∧
      gap coords low p c = 1 / 4 ∧
      gap coords low p c ≤ 3 / 16 + 1 / 4 := by
  refine ⟨{0}, {0}, fun _ _ => 0, fun _ => 1 / 4, fun _ => 0,
          fun _ => -1, fun _ => -(3 / 4), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c₀ w _; simp [pair]
  · intro c₀; exact ⟨0, by simp, by simp [pair]⟩
  · intro w _ k _; norm_num
  · simp only [l1, Finset.sum_singleton]
    rw [show (-1 : ℚ) - -(3 / 4) = -(1 / 4) by ring, abs_neg]
    norm_num
  · simp [gap, pair]; norm_num
  · simp [gap, pair]
  · simp [gap, pair]; norm_num

end Workspace.Normativity.Contrib.CoherenceModulus

#print axioms Workspace.Normativity.Contrib.CoherenceModulus.l1_nonneg
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.abs_pair_le_l1_mul
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_net
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_net_cover
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_nonpos_at_world
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.net_modulus_is_nonvacuous
