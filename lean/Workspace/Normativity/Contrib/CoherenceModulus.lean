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
    (Wld : ι → κ → ℚ) (p : κ → ℚ) (low : (κ → ℚ) → ℚ) (net : Set (κ → ℚ))
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

/-! ## Mixtures, and the two halves of the exact theorem

`dist_∞(p, conv V) ≤ δ` says exactly that some mixture of the worlds is within `δ`
of the price in every priced coordinate.  That is the form the deductive coherence
statement wants — "there is an admissible credence whose expectations are within
`δ` of the displayed prices" — and it is the form used below, so that no metric
space or closure has to be set up.

**Soundness** is elementary and proved here: no support-function row can ever
report more than the distance, so a row family cannot overstate incoherence.

**Exactness** — that some finite row family reports the distance for every price —
is the other half.  It is `DistanceComplete` below, stated at the type the force
theorem consumes.  It is *not* proved here: it is convex duality for a finite
rational polytope, and the round establishes it on paper and by exhaustive
verification over rational grids (`tests/test_coherence.py`) rather than in the
kernel.  What is proved here is that the interface cannot be satisfied vacuously,
since soundness forces any witnessing `δ` to be at least the distance. -/

/-- The mixture of the worlds under a weight vector, coordinate by coordinate. -/
def mixture (worlds : Finset ι) (Wld : ι → κ → ℚ) (μ : ι → ℚ) : κ → ℚ :=
  fun k => ∑ w ∈ worlds, μ w * Wld w k

/-- A weight vector is a credence on the worlds. -/
structure IsCredence (worlds : Finset ι) (μ : ι → ℚ) : Prop where
  nonneg : ∀ w ∈ worlds, 0 ≤ μ w
  total : ∑ w ∈ worlds, μ w = 1

lemma pair_mixture (coords : Finset κ) (worlds : Finset ι) (Wld : ι → κ → ℚ)
    (μ : ι → ℚ) (c : κ → ℚ) :
    pair coords c (mixture worlds Wld μ) =
      ∑ w ∈ worlds, μ w * pair coords c (Wld w) := by
  unfold pair mixture
  calc ∑ k ∈ coords, c k * ∑ w ∈ worlds, μ w * Wld w k
      = ∑ k ∈ coords, ∑ w ∈ worlds, μ w * (c k * Wld w k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring
    _ = ∑ w ∈ worlds, ∑ k ∈ coords, μ w * (c k * Wld w k) := Finset.sum_comm
    _ = ∑ w ∈ worlds, μ w * ∑ k ∈ coords, c k * Wld w k := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]

/-- A lower envelope of the worlds is a lower envelope of every mixture of them. -/
lemma low_le_pair_mixture (coords : Finset κ) (worlds : Finset ι) (Wld : ι → κ → ℚ)
    (low : (κ → ℚ) → ℚ)
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w))
    (μ : ι → ℚ) (hμ : IsCredence worlds μ) (c : κ → ℚ) :
    low c ≤ pair coords c (mixture worlds Wld μ) := by
  rw [pair_mixture]
  calc low c = ∑ w ∈ worlds, μ w * low c := by
        rw [← Finset.sum_mul, hμ.total, one_mul]
    _ ≤ ∑ w ∈ worlds, μ w * pair coords c (Wld w) :=
        Finset.sum_le_sum fun w hw =>
          mul_le_mul_of_nonneg_left (hlow_le c w hw) (hμ.nonneg w hw)

/-- **Soundness: a support-function row never overstates the distance.**  If some
credence's mixture is within `B` of the price in every priced coordinate, then every
coefficient vector in the unit `ℓ¹` ball has support gap at most `B`.

Contrapositive, and the reason the row family is worth compiling: a violation of
`δ` on any row certifies that *no* admissible credence is within `δ` of the
displayed price. -/
theorem gap_le_of_mixture (coords : Finset κ) (worlds : Finset ι) (Wld : ι → κ → ℚ)
    (p : κ → ℚ) (low : (κ → ℚ) → ℚ)
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w))
    (μ : ι → ℚ) (hμ : IsCredence worlds μ) {B : ℚ} (hB : 0 ≤ B)
    (hclose : ∀ k ∈ coords, |mixture worlds Wld μ k - p k| ≤ B)
    (c : κ → ℚ) (hc : l1 coords c ≤ 1) :
    gap coords low p c ≤ B := by
  have hlowmix := low_le_pair_mixture coords worlds Wld low hlow_le μ hμ c
  have hHolder : |pair coords c (fun k => mixture worlds Wld μ k - p k)|
      ≤ l1 coords c * B :=
    abs_pair_le_l1_mul coords c _ hB hclose
  have hle : pair coords c (fun k => mixture worlds Wld μ k - p k) ≤ B := by
    have h := (abs_le.mp hHolder).2
    have hmul : l1 coords c * B ≤ 1 * B := mul_le_mul_of_nonneg_right hc hB
    rw [one_mul] at hmul
    exact h.trans hmul
  rw [pair_sub] at hle
  unfold gap
  linarith

/-- A row family is **distance-complete** for the worlds when per-row conformance
at any tolerance exhibits a credence that close.  For the exact dual-distance
family of a rational polytope this holds with no error term; for a support-function
net it holds with the mesh added, which is `gap_le_of_net_cover`. -/
def DistanceComplete (coords : Finset κ) (worlds : Finset ι) (Wld : ι → κ → ℚ)
    (low : (κ → ℚ) → ℚ) (net : Set (κ → ℚ)) : Prop :=
  ∀ (p : κ → ℚ) (δ : ℚ), 0 ≤ δ → (∀ c ∈ net, gap coords low p c ≤ δ) →
    ∃ μ : ι → ℚ, IsCredence worlds μ ∧
      ∀ k ∈ coords, |mixture worlds Wld μ k - p k| ≤ δ

/-- The interface cannot be met vacuously: a distance-complete family's witnessing
tolerance is at least the support gap of every unit-`ℓ¹` coefficient vector, so it
is at least the distance the family is claiming to certify. -/
theorem gap_le_of_distanceComplete (coords : Finset κ) (worlds : Finset ι)
    (Wld : ι → κ → ℚ) (low : (κ → ℚ) → ℚ) (net : Set (κ → ℚ))
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w))
    (hcomplete : DistanceComplete coords worlds Wld low net)
    (p : κ → ℚ) (δ : ℚ) (hδ : 0 ≤ δ) (hconf : ∀ c ∈ net, gap coords low p c ≤ δ)
    (c : κ → ℚ) (hc : l1 coords c ≤ 1) :
    gap coords low p c ≤ δ := by
  obtain ⟨μ, hμ, hclose⟩ := hcomplete p δ hδ hconf
  exact gap_le_of_mixture coords worlds Wld p low hlow_le μ hμ hδ hclose c hc

/-- **The intrinsic reading of per-row conformance.**  Under a distance-complete
row family, conformance at `δ` on every row is exactly the statement the deductive
coherence result wants: some admissible credence's expectations are within `δ` of
the displayed prices in every priced coordinate. -/
theorem exists_credence_of_conformance (coords : Finset κ) (worlds : Finset ι)
    (Wld : ι → κ → ℚ) (low : (κ → ℚ) → ℚ) (net : Set (κ → ℚ))
    (hcomplete : DistanceComplete coords worlds Wld low net)
    (p : κ → ℚ) (δ : ℚ) (hδ : 0 ≤ δ)
    (hconf : ∀ c ∈ net, gap coords low p c ≤ δ) :
    ∃ μ : ι → ℚ, IsCredence worlds μ ∧
      ∀ k ∈ coords, |mixture worlds Wld μ k - p k| ≤ δ :=
  hcomplete p δ hδ hconf

/-- A support-function net is distance-complete up to its mesh, which is the
fallback when no exact family is available.  Stated as the composition of
`gap_le_of_net_cover` with whatever exactness the unit ball itself provides, so the
mesh appears once and additively. -/
theorem gap_le_of_net_cover_add (coords : Finset κ) (worlds : Finset ι)
    (Wld : ι → κ → ℚ) (p : κ → ℚ) (low : (κ → ℚ) → ℚ) (net : Set (κ → ℚ))
    (hlow_le : ∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w))
    (hlow_att : ∀ c, ∃ w ∈ worlds, low c = pair coords c (Wld w))
    (hcube : ∀ w ∈ worlds, ∀ k ∈ coords, |Wld w k - p k| ≤ 1)
    {δ mesh : ℚ} (hmesh : 0 ≤ mesh)
    (hconf : ∀ c' ∈ net, gap coords low p c' ≤ δ)
    (hcover : ∀ c : κ → ℚ, l1 coords c ≤ 1 →
      ∃ c' ∈ net, l1 coords (fun k => c k - c' k) ≤ mesh)
    (c : κ → ℚ) (hc : l1 coords c ≤ 1) :
    gap coords low p c ≤ δ + mesh :=
  gap_le_of_net_cover coords worlds Wld p low net hlow_le hlow_att hcube hmesh
    hconf hcover c hc

/-- Inhabitation of the mixture side: one coordinate, worlds `0` and `1`, the
credence `(1/4, 3/4)` whose mixture is `3/4`, and the price `1/2`, so every unit
coefficient vector has support gap at most `1/4`. -/
theorem mixture_soundness_is_nonvacuous :
    ∃ (coords : Finset ℕ) (worlds : Finset ℕ) (Wld : ℕ → ℕ → ℚ) (p : ℕ → ℚ)
      (low : (ℕ → ℚ) → ℚ) (μ : ℕ → ℚ),
      IsCredence worlds μ ∧
      (∀ c, ∀ w ∈ worlds, low c ≤ pair coords c (Wld w)) ∧
      mixture worlds Wld μ 0 = 3 / 4 ∧
      (∀ k ∈ coords, |mixture worlds Wld μ k - p k| ≤ 1 / 4) := by
  refine ⟨{0}, {0, 1}, fun w _ => (w : ℚ), fun _ => 1 / 2,
          fun c => min (c 0 * 0) (c 0 * 1), fun w => if w = 0 then 1 / 4 else 3 / 4,
          ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> norm_num
  · norm_num
  · intro c w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simpa [pair] using min_le_left (c 0 * 0) (c 0 * 1)
    · simpa [pair] using min_le_right (c 0 * 0) (c 0 * 1)
  · simp [mixture]
  · intro k hk
    simp only [Finset.mem_singleton] at hk
    subst hk
    norm_num [mixture]

end Workspace.Normativity.Contrib.CoherenceModulus

#print axioms Workspace.Normativity.Contrib.CoherenceModulus.l1_nonneg
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.abs_pair_le_l1_mul
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_net
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_net_cover
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_nonpos_at_world
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.net_modulus_is_nonvacuous
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.pair_mixture
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.low_le_pair_mixture
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_mixture
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_distanceComplete
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.exists_credence_of_conformance
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.gap_le_of_net_cover_add
#print axioms Workspace.Normativity.Contrib.CoherenceModulus.mixture_soundness_is_nonvacuous
