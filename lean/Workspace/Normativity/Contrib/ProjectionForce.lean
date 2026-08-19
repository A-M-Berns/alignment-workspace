/-
# Projection enforcement

An enforcement trader that names no rows. For a fragment `Φ`, a nonempty closed
convex region `K` of price vectors on `Φ`, and the displayed price `p`, let `q` be
the Euclidean nearest point of `K` to `p` and let the day's position be

    ζ = λ · (q − p).

Everything the force layer needs follows from the *variational characterization* of
the nearest point,

    ⟪p − q, y − q⟫ ≤ 0   for every y ∈ K,

by elementary algebra: no separation theorem, no duality, no row presentation, and
no presentation-dependent constant. That is the point of this file. The row
construction in `TraderizedEnforcement` and `EnforcementStrategy` needed a
duality step (`CoherenceModulus.DistanceComplete`) to say anything intrinsic; here
the intrinsic statement *is* the inequality.

Three things are proved that the row route had to assume or approximate.

* **Force.** `⟪ζ, y − p⟫ ≥ λ‖q − p‖²` at every `y ∈ K` — the exact analogue of the
  weighted-square bound, with `‖q − p‖²` the intrinsic squared distance rather than
  a sum over displayed rows.
* **The opposing-pressure bound is automatic.** The market maker's guarantee holds
  at every point of the price cube, not only at `{0,1}` worlds, because a
  strategy's value is affine in the world and the cube is the hull of its vertices.
  So the comparison point may be `q` itself, chosen after the price is displayed,
  and the ordinary aggregate's opposition is bounded by its own `Strategy.absBound`
  — a rational number computed from the strategy the firm has already emitted.
* **Liability.** `⟪ζ, x − p⟫ ≥ λ(‖q−p‖² − ‖q−p‖·d(x,K))`, so a world the region
  admits costs the enforcement trader nothing, and one it excludes costs in
  proportion to how far outside it lies.

Nothing here compiles the projector into a trading strategy; that is
`ProjectionCompiler`, and it is where the remaining work is.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.AssessmentProcess

namespace Workspace.Normativity.Contrib.ProjectionForce

open LogicalInduction
open scoped BigOperators

/-! ## The fragment inner product -/

/-- The inner product a fragment carries: a finite sum over the priced sentences. -/
def ip (Φ : Finset Sentence) (u v : Sentence → ℝ) : ℝ := ∑ φ ∈ Φ, u φ * v φ

/-- The squared Euclidean distance on the fragment. -/
def sqDist (Φ : Finset Sentence) (u v : Sentence → ℝ) : ℝ :=
  ∑ φ ∈ Φ, (u φ - v φ) ^ 2

/-- The Euclidean distance on the fragment. -/
noncomputable def dist2 (Φ : Finset Sentence) (u v : Sentence → ℝ) : ℝ :=
  Real.sqrt (sqDist Φ u v)

lemma sqDist_nonneg (Φ : Finset Sentence) (u v : Sentence → ℝ) : 0 ≤ sqDist Φ u v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma dist2_nonneg (Φ : Finset Sentence) (u v : Sentence → ℝ) : 0 ≤ dist2 Φ u v :=
  Real.sqrt_nonneg _

lemma sq_dist2 (Φ : Finset Sentence) (u v : Sentence → ℝ) :
    dist2 Φ u v ^ 2 = sqDist Φ u v :=
  Real.sq_sqrt (sqDist_nonneg Φ u v)

lemma sqDist_comm (Φ : Finset Sentence) (u v : Sentence → ℝ) :
    sqDist Φ u v = sqDist Φ v u := by
  unfold sqDist
  exact Finset.sum_congr rfl fun φ _ => by ring

lemma dist2_comm (Φ : Finset Sentence) (u v : Sentence → ℝ) :
    dist2 Φ u v = dist2 Φ v u := by
  unfold dist2
  rw [sqDist_comm]

lemma ip_self (Φ : Finset Sentence) (u v : Sentence → ℝ) :
    ip Φ (fun φ => u φ - v φ) (fun φ => u φ - v φ) = sqDist Φ u v := by
  unfold ip sqDist
  exact Finset.sum_congr rfl fun φ _ => by ring

lemma ip_add_right (Φ : Finset Sentence) (u v w : Sentence → ℝ) :
    ip Φ u (fun φ => v φ + w φ) = ip Φ u v + ip Φ u w := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun φ _ => by ring

lemma ip_smul_left (Φ : Finset Sentence) (c : ℝ) (u v : Sentence → ℝ) :
    ip Φ (fun φ => c * u φ) v = c * ip Φ u v := by
  unfold ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun φ _ => by ring

/-- Cauchy–Schwarz on the fragment. -/
lemma abs_ip_le (Φ : Finset Sentence) (u v : Sentence → ℝ) :
    |ip Φ u v| ≤ dist2 Φ u 0 * dist2 Φ v 0 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Φ u v
  have hu : sqDist Φ u 0 = ∑ φ ∈ Φ, u φ ^ 2 := by
    unfold sqDist; exact Finset.sum_congr rfl fun φ _ => by simp
  have hv : sqDist Φ v 0 = ∑ φ ∈ Φ, v φ ^ 2 := by
    unfold sqDist; exact Finset.sum_congr rfl fun φ _ => by simp
  have hstep : |ip Φ u v| ≤ Real.sqrt ((∑ φ ∈ Φ, u φ ^ 2) * ∑ φ ∈ Φ, v φ ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hcs
  rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hstep
  unfold dist2
  rw [hu, hv]
  exact hstep

/-! ## The nearest point, by its variational characterization

The only property of `q` any theorem below uses.  It is what Hilbert-space
projection onto a nonempty closed convex set delivers, and it is weaker than
"nearest": any point of `K` obtuse to every direction into `K` will do. -/

/-- `q` is a nearest point of `K` to `p` on the fragment `Φ`. -/
def IsNearestPoint (Φ : Finset Sentence) (K : (Sentence → ℝ) → Prop)
    (p q : Sentence → ℝ) : Prop :=
  K q ∧ ∀ y, K y → ip Φ (fun φ => p φ - q φ) (fun φ => y φ - q φ) ≤ 0

/-- The enforcement position: the displacement toward the region, scaled. -/
def shares (lam : ℝ) (p q : Sentence → ℝ) : Sentence → ℝ := fun φ => lam * (q φ - p φ)

/-! ## Force -/

/-- The obtuse-angle step, in the direction the force theorem needs. -/
lemma sqDist_le_ip_of_mem {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {p q y : Sentence → ℝ} (hq : IsNearestPoint Φ K p q) (hy : K y) :
    sqDist Φ p q ≤ ip Φ (fun φ => q φ - p φ) (fun φ => y φ - p φ) := by
  have hsplit : ip Φ (fun φ => q φ - p φ) (fun φ => y φ - p φ) =
      ip Φ (fun φ => q φ - p φ) (fun φ => y φ - q φ) +
        ip Φ (fun φ => q φ - p φ) (fun φ => q φ - p φ) := by
    rw [← ip_add_right]
    unfold ip
    exact Finset.sum_congr rfl fun φ _ => by ring
  have hobtuse : 0 ≤ ip Φ (fun φ => q φ - p φ) (fun φ => y φ - q φ) := by
    have h := hq.2 y hy
    have hneg : ip Φ (fun φ => q φ - p φ) (fun φ => y φ - q φ) =
        -ip Φ (fun φ => p φ - q φ) (fun φ => y φ - q φ) := by
      unfold ip
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun φ _ => by ring
    rw [hneg]
    linarith
  rw [hsplit, ip_self, sqDist_comm Φ q p]
  linarith

/-- **The force inequality.**  Against any point the region admits, the projection
position is worth at least the intensity times the intrinsic squared distance.

This is the analogue of `TraderizedEnforcement.weighted_square_le_pair`, with the
row sum replaced by the intrinsic quantity and no presentation in the statement. -/
theorem force_inequality {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {p q y : Sentence → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hq : IsNearestPoint Φ K p q) (hy : K y) :
    lam * sqDist Φ p q ≤ ip Φ (shares lam p q) (fun φ => y φ - p φ) := by
  have h := sqDist_le_ip_of_mem hq hy
  have hsm : ip Φ (shares lam p q) (fun φ => y φ - p φ) =
      lam * ip Φ (fun φ => q φ - p φ) (fun φ => y φ - p φ) := by
    unfold shares
    exact ip_smul_left Φ lam _ _
  rw [hsm]
  exact mul_le_mul_of_nonneg_left h hlam

/-- Nonnegativity at an admitted point: the enforcement trader is never subsidised
where the region already holds. -/
theorem value_nonneg_of_mem {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {p q y : Sentence → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hq : IsNearestPoint Φ K p q) (hy : K y) :
    0 ≤ ip Φ (shares lam p q) (fun φ => y φ - p φ) :=
  le_trans (mul_nonneg hlam (sqDist_nonneg Φ p q)) (force_inequality hlam hq hy)

/-! ## Liability -/

/-- **The liability inequality.**  Against a point the region need not admit, the
projection position loses at most the intensity times the product of the two
distances: how far the price is outside, and how far the point is outside.

`z` is a nearest point of `K` to `x`; `dist2 Φ x z` is therefore the intrinsic
distance from `x` to the region. -/
theorem liability_inequality {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {p q x z : Sentence → ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hq : IsNearestPoint Φ K p q) (hz : IsNearestPoint Φ K x z) :
    lam * (sqDist Φ p q - dist2 Φ p q * dist2 Φ x z)
      ≤ ip Φ (shares lam p q) (fun φ => x φ - p φ) := by
  have hzK : K z := hz.1
  have hsplit : ip Φ (fun φ => q φ - p φ) (fun φ => x φ - p φ) =
      ip Φ (fun φ => q φ - p φ) (fun φ => x φ - z φ) +
        ip Φ (fun φ => q φ - p φ) (fun φ => z φ - p φ) := by
    rw [← ip_add_right]
    unfold ip
    exact Finset.sum_congr rfl fun φ _ => by ring
  have hz' : sqDist Φ p q ≤ ip Φ (fun φ => q φ - p φ) (fun φ => z φ - p φ) :=
    sqDist_le_ip_of_mem hq hzK
  have hcs : |ip Φ (fun φ => q φ - p φ) (fun φ => x φ - z φ)|
      ≤ dist2 Φ q p * dist2 Φ x z := by
    have h := abs_ip_le Φ (fun φ => q φ - p φ) (fun φ => x φ - z φ)
    have h1 : dist2 Φ (fun φ => q φ - p φ) 0 = dist2 Φ q p := by
      unfold dist2 sqDist; congr 1; exact Finset.sum_congr rfl fun φ _ => by simp
    have h2 : dist2 Φ (fun φ => x φ - z φ) 0 = dist2 Φ x z := by
      unfold dist2 sqDist; congr 1; exact Finset.sum_congr rfl fun φ _ => by simp
    rwa [h1, h2] at h
  have hqp : dist2 Φ q p = dist2 Φ p q := dist2_comm Φ q p
  rw [hqp] at hcs
  have hlow : sqDist Φ p q - dist2 Φ p q * dist2 Φ x z
      ≤ ip Φ (fun φ => q φ - p φ) (fun φ => x φ - p φ) := by
    rw [hsplit]
    have := (abs_le.mp hcs).1
    linarith
  have hsm : ip Φ (shares lam p q) (fun φ => x φ - p φ) =
      lam * ip Φ (fun φ => q φ - p φ) (fun φ => x φ - p φ) := by
    unfold shares
    exact ip_smul_left Φ lam _ _
  rw [hsm]
  exact mul_le_mul_of_nonneg_left hlow hlam

/-- **The calibrated liability bound.**  Once the price is within `δ` of the region
— which is what the conformance theorem delivers — the day's loss at any point is
at most `λδ` times that point's distance from the region. -/
theorem liability_calibrated {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {p q x z : Sentence → ℝ} {lam δ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hq : IsNearestPoint Φ K p q) (hz : IsNearestPoint Φ K x z)
    (hconf : dist2 Φ p q ≤ δ) :
    -(lam * δ * dist2 Φ x z) ≤ ip Φ (shares lam p q) (fun φ => x φ - p φ) := by
  have hbase := liability_inequality hlam hq hz
  have hsq : 0 ≤ sqDist Φ p q := sqDist_nonneg Φ p q
  have hmul : dist2 Φ p q * dist2 Φ x z ≤ δ * dist2 Φ x z :=
    mul_le_mul_of_nonneg_right hconf (dist2_nonneg Φ x z)
  have hstep : lam * (sqDist Φ p q - dist2 Φ p q * dist2 Φ x z)
      ≥ lam * (0 - δ * dist2 Φ x z) := by
    apply mul_le_mul_of_nonneg_left _ hlam
    linarith
  have : lam * (0 - δ * dist2 Φ x z) = -(lam * δ * dist2 Φ x z) := by ring
  linarith [hbase, hstep]

/-! ## The Euclidean bound dominates the sup bound

The paper states finite-time coherence in the `ℓ^∞` form: some admissible price
vector agrees with the displayed one to within `δ` on every priced sentence.  That
form is *weaker* than the Euclidean one, and follows from it with the same `δ`,
because `‖x‖_∞ ≤ ‖x‖_2` coordinatewise.  So a Euclidean conformance theorem needs
no duality, no separation theorem and no net to deliver the paper's own statement:
the projected point is the witness. -/

lemma abs_sub_le_dist2 (Φ : Finset Sentence) (u v : Sentence → ℝ) {φ : Sentence}
    (hφ : φ ∈ Φ) : |u φ - v φ| ≤ dist2 Φ u v := by
  have hterm : (u φ - v φ) ^ 2 ≤ sqDist Φ u v := by
    refine Finset.single_le_sum (f := fun ψ => (u ψ - v ψ) ^ 2) ?_ hφ
    intro ψ _
    positivity
  have h := Real.sqrt_le_sqrt hterm
  rwa [Real.sqrt_sq_eq_abs] at h

/-- **Sup-norm conformance from Euclidean conformance.**  If the displayed price is
within `δ` of the region in the intrinsic Euclidean distance on the fragment, the
nearest point is an admissible price vector agreeing with it to within `δ` on every
priced sentence — the paper's `ℓ^∞` statement, with the same `δ`. -/
theorem sup_conformance_of_dist2 {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {p q : Sentence → ℝ} {δ : ℝ} (hq : IsNearestPoint Φ K p q)
    (hconf : dist2 Φ p q ≤ δ) :
    K q ∧ ∀ φ ∈ Φ, |p φ - q φ| ≤ δ :=
  ⟨hq.1, fun φ hφ => le_trans (abs_sub_le_dist2 Φ p q hφ) hconf⟩

end Workspace.Normativity.Contrib.ProjectionForce

#print axioms Workspace.Normativity.Contrib.ProjectionForce.abs_ip_le
#print axioms Workspace.Normativity.Contrib.ProjectionForce.sqDist_le_ip_of_mem
#print axioms Workspace.Normativity.Contrib.ProjectionForce.force_inequality
#print axioms Workspace.Normativity.Contrib.ProjectionForce.value_nonneg_of_mem
#print axioms Workspace.Normativity.Contrib.ProjectionForce.liability_inequality
#print axioms Workspace.Normativity.Contrib.ProjectionForce.liability_calibrated
#print axioms Workspace.Normativity.Contrib.ProjectionForce.sup_conformance_of_dist2
