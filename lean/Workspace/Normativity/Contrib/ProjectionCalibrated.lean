/-
# The calibrated construction

`ProjectionMarket` and `ProjectionBudget` carry a free intensity `λ` and an assumed
tolerance, which is the right generality for the algebra and the wrong shape for a paper
statement.  This file pins the intensity to the least value that buys the day's tolerance
and reads the budget off at that value, so the paper-facing charge carries no free
parameter:

    ρ_n = ε_n + A_n,      λ_n = ρ_n / δ_n²,      b_n(W) = (ρ_n / δ_n) · d₂(W|_Φ, K_n).

`ρ_n` is *market resistance*: the market maker's own slack plus the ordinary aggregate's
computable syntactic bound.  Both are rational, so `λ_n` is a legal constant in a compiled
expressible feature.

It also makes the cube extension explicit.  The enforcement trader is a statement about
the fragment, but `Strategy.abs_value_le` evaluates the ordinary aggregate at the whole
comparison point, and that aggregate need not trade inside the fragment.  So the point fed
to the market maker's contract is the fragment target **extended off the fragment by the
displayed prices**.  That extension is a bookkeeping device for one inequality; it is not
a credence, and no conclusion is drawn about its coordinates outside the fragment.  The
credal conclusion is about the fragment projection, and only that.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ProjectionBudget

namespace Workspace.Normativity.Contrib.ProjectionCalibrated

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionMarket
open Workspace.Normativity.Contrib.ProjectionBudget

/-! ## The cube extension

A region reached by projecting a credal set onto a fragment constrains the fragment's
coordinates and nothing else.  `FragmentLocal` says exactly that, and it is what makes the
extension legitimate. -/

/-- The region constrains only the fragment's coordinates. -/
def FragmentLocal (Φ : Finset Sentence) (K : (Sentence → ℝ) → Prop) : Prop :=
  ∀ u v : Sentence → ℝ, (∀ φ ∈ Φ, u φ = v φ) → K u → K v

/-- The fragment target `q`, extended off the fragment by the displayed prices `p`.  A
device for evaluating one inequality at a legal cube point — never a credence. -/
def extend (Φ : Finset Sentence) (p q : Sentence → ℝ) : Sentence → ℝ :=
  fun φ => if φ ∈ Φ then q φ else p φ

lemma extend_of_mem {Φ : Finset Sentence} {p q : Sentence → ℝ} {φ : Sentence}
    (h : φ ∈ Φ) : extend Φ p q φ = q φ := if_pos h

lemma extend_of_not_mem {Φ : Finset Sentence} {p q : Sentence → ℝ} {φ : Sentence}
    (h : φ ∉ Φ) : extend Φ p q φ = p φ := if_neg h

lemma ip_extend (Φ : Finset Sentence) (p q u : Sentence → ℝ) :
    ip Φ (fun φ => extend Φ p q φ - p φ) u = ip Φ (fun φ => q φ - p φ) u :=
  Finset.sum_congr rfl fun φ hφ => by simp only [extend_of_mem hφ]

lemma sqDist_extend (Φ : Finset Sentence) (p q : Sentence → ℝ) :
    sqDist Φ p (extend Φ p q) = sqDist Φ p q :=
  Finset.sum_congr rfl fun φ hφ => by simp only [extend_of_mem hφ]

lemma dist2_extend (Φ : Finset Sentence) (p q : Sentence → ℝ) :
    dist2 Φ p (extend Φ p q) = dist2 Φ p q := by
  unfold dist2; rw [sqDist_extend]

/-- The extension is a legal cube point whenever the displayed prices are and the target's
fragment coordinates are. -/
lemma extend_mem_cube {Φ : Finset Sentence} {p q : Sentence → ℝ}
    (hp : ∀ φ, 0 ≤ p φ ∧ p φ ≤ 1) (hq : ∀ φ ∈ Φ, 0 ≤ q φ ∧ q φ ≤ 1) :
    ∀ φ, 0 ≤ extend Φ p q φ ∧ extend Φ p q φ ≤ 1 := by
  intro φ
  by_cases hφ : φ ∈ Φ
  · rw [extend_of_mem hφ]; exact hq φ hφ
  · rw [extend_of_not_mem hφ]; exact hp φ

/-- Extending a nearest point off the fragment leaves it a nearest point. -/
lemma isNearestPoint_extend {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {p q : Sentence → ℝ} (hlocal : FragmentLocal Φ K)
    (h : IsNearestPoint Φ K p q) : IsNearestPoint Φ K p (extend Φ p q) := by
  refine ⟨hlocal q (extend Φ p q) (fun φ hφ => (extend_of_mem hφ).symm) h.1, ?_⟩
  intro y hy
  have := h.2 y hy
  refine le_trans (le_of_eq ?_) this
  exact Finset.sum_congr rfl fun φ hφ => by simp only [extend_of_mem hφ]

/-- Realizing the extended target is realizing the target: the trader only ever sees the
fragment. -/
lemma realizes_extend {Φ : Finset Sentence} {lam : ℝ} {q : Sentence → ℝ} {n : ℕ}
    {T : Strategy n} {V : History} :
    Realizes Φ lam (extend Φ (V n) q) T V ↔ Realizes Φ lam q T V := by
  constructor <;> intro h w <;> rw [h w] <;> unfold ip shares <;>
    exact Finset.sum_congr rfl fun φ hφ => by simp only [extend_of_mem hφ]

/-! ## Market resistance and the calibrated intensity -/

/-- **Market resistance** on day `n`: the market maker's own slack plus the ordinary
aggregate's computable syntactic bound.  Rational, and available before the day's price. -/
def resistance (n : ℕ) (A : ℚ) : ℚ := marketMakerError n + A

/-- The **calibrated intensity** `ρ_n / δ_n²` — the least intensity that buys tolerance
`δ_n`.  The paper's construction uses this value, not an arbitrary larger one. -/
def calibratedIntensity (n : ℕ) (A δ : ℚ) : ℚ := resistance n A / δ ^ 2

lemma resistance_pos {n : ℕ} {A : ℚ} (hA : 0 ≤ A) : 0 < resistance n A := by
  have := marketMakerError_pos n
  unfold resistance; linarith

lemma calibratedIntensity_pos {n : ℕ} {A δ : ℚ} (hA : 0 ≤ A) (hδ : 0 < δ) :
    0 < calibratedIntensity n A δ :=
  div_pos (resistance_pos hA) (by positivity)

/-- The day's charge coefficient: at the calibrated intensity, `λ_n · δ_n = ρ_n / δ_n`.
This is the equality the paper-facing budget needs, and it holds **only** at the
calibrated value — under a mere lower bound on `λ_n` the two sides differ. -/
lemma calibratedIntensity_mul (n : ℕ) (A : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    calibratedIntensity n A δ * δ = resistance n A / δ := by
  unfold calibratedIntensity
  field_simp

/-! ## The calibrated market theorem

The tolerance is bought without assuming the target is a legal cube point: that is
discharged from the region lying in the cube on the fragment, together with the market's
own prices lying in the cube. -/

theorem dist2_le_of_calibrated
    (Tr : Trader) (n : ℕ) {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {δ : ℚ} {A : ℚ} {q : Sentence → ℝ} (ord enf : Strategy n)
    (hjoin : Tr.strat n = Strategy.join [ord, enf])
    (hlocal : FragmentLocal Φ K)
    (hKcube : ∀ y, K y → ∀ φ ∈ Φ, 0 ≤ y φ ∧ y φ ≤ 1)
    (hq : IsNearestPoint Φ K (marketMakerHistory Tr n) q)
    (henf : Realizes Φ ((calibratedIntensity n A δ : ℚ) : ℝ) q enf
      (marketMakerHistory Tr))
    (hA : (ord.absBound : ℚ) ≤ A) (hδ : 0 < δ) :
    dist2 Φ (marketMakerHistory Tr n) q ≤ (δ : ℝ) := by
  have hAnn : (0 : ℚ) ≤ A := le_trans (Strategy.absBound_nonneg ord) hA
  have hp := marketMakerHistory_mem_Icc Tr n
  have hqcube : ∀ φ, 0 ≤ extend Φ (marketMakerHistory Tr n) q φ ∧
      extend Φ (marketMakerHistory Tr n) q φ ≤ 1 :=
    extend_mem_cube hp (fun φ hφ => hKcube q hq.1 φ hφ)
  have hqext := isNearestPoint_extend hlocal hq
  have henfext : Realizes Φ ((calibratedIntensity n A δ : ℚ) : ℝ)
      (extend Φ (marketMakerHistory Tr n) q) enf (marketMakerHistory Tr) :=
    realizes_extend.mpr henf
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hbound : ((marketMakerError n : ℝ) + (ord.absBound : ℝ)) / (δ : ℝ) ^ 2
      ≤ ((calibratedIntensity n A δ : ℚ) : ℝ) := by
    have hnum : (marketMakerError n : ℝ) + (ord.absBound : ℝ)
        ≤ ((resistance n A : ℚ) : ℝ) := by
      have : ((ord.absBound : ℚ) : ℝ) ≤ ((A : ℚ) : ℝ) := by exact_mod_cast hA
      unfold resistance
      push_cast
      linarith
    have hden : (0 : ℝ) < (δ : ℝ) ^ 2 := by positivity
    have : ((calibratedIntensity n A δ : ℚ) : ℝ)
        = ((resistance n A : ℚ) : ℝ) / (δ : ℝ) ^ 2 := by
      unfold calibratedIntensity; push_cast; ring
    rw [this]
    exact div_le_div_of_nonneg_right hnum hden.le
  have := dist2_le_of_intensity Tr n ord enf hjoin henfext hqext hqcube hδR hbound
  rwa [dist2_extend] at this

/-! ## The calibrated budget

The paper-facing statement.  The day-`k` charge is market resistance over requested
tolerance, times the assessed point's intrinsic distance from the day-`k` region.  No free
intensity appears, and no relation between the regions at different dates is assumed. -/

theorem cumValue_ge_of_calibrated (E : Trader) (V : History)
    {Φ : ℕ → Finset Sentence} {K : ℕ → (Sentence → ℝ) → Prop}
    {A δ : ℕ → ℚ} {q z : ℕ → Sentence → ℝ} (w : Sentence → ℝ) (n : ℕ)
    (hA : ∀ k, k ≤ n → 0 ≤ A k) (hδ : ∀ k, k ≤ n → 0 < δ k)
    (henf : ∀ k, k ≤ n → Realizes (Φ k)
      ((calibratedIntensity k (A k) (δ k) : ℚ) : ℝ) (q k) (E.strat k) V)
    (hq : ∀ k, k ≤ n → IsNearestPoint (Φ k) (K k) (V k) (q k))
    (hz : ∀ k, k ≤ n → IsNearestPoint (Φ k) (K k) w (z k))
    (hconf : ∀ k, k ≤ n → dist2 (Φ k) (V k) (q k) ≤ ((δ k : ℚ) : ℝ)) :
    -(∑ k ∈ Finset.range (n + 1),
        ((resistance k (A k) / δ k : ℚ) : ℝ) * dist2 (Φ k) w (z k))
      ≤ cumValue E V w n := by
  refine cumValue_ge_of_dayBounds E V w
    (fun k => ((resistance k (A k) / δ k : ℚ) : ℝ) * dist2 (Φ k) w (z k)) n ?_
  intro k hk
  have hlam : (0 : ℝ) ≤ ((calibratedIntensity k (A k) (δ k) : ℚ) : ℝ) := by
    exact_mod_cast (calibratedIntensity_pos (hA k hk) (hδ k hk)).le
  have hδR : (0 : ℝ) ≤ ((δ k : ℚ) : ℝ) := by exact_mod_cast (hδ k hk).le
  have hbase := day_value_ge (henf k hk) hlam hδR (hq k hk) w (hz k hk) (hconf k hk)
  have hcoef : ((calibratedIntensity k (A k) (δ k) : ℚ) : ℝ) * ((δ k : ℚ) : ℝ)
      = ((resistance k (A k) / δ k : ℚ) : ℝ) := by
    have := calibratedIntensity_mul k (A k) (hδ k hk)
    exact_mod_cast congrArg (fun r : ℚ => (r : ℝ)) this
  rwa [hcoef] at hbase

/-- The calibrated zero-risk-capital statement: per-date admission still gives a budget of
exactly zero, and the calibration changes nothing about it. -/
theorem cumValue_nonneg_of_calibrated (E : Trader) (V : History)
    {Φ : ℕ → Finset Sentence} {K : ℕ → (Sentence → ℝ) → Prop}
    {A δ : ℕ → ℚ} {q : ℕ → Sentence → ℝ} (w : Sentence → ℝ) (n : ℕ)
    (hA : ∀ k, k ≤ n → 0 ≤ A k) (hδ : ∀ k, k ≤ n → 0 < δ k)
    (henf : ∀ k, k ≤ n → Realizes (Φ k)
      ((calibratedIntensity k (A k) (δ k) : ℚ) : ℝ) (q k) (E.strat k) V)
    (hq : ∀ k, k ≤ n → IsNearestPoint (Φ k) (K k) (V k) (q k))
    (hw : ∀ k, k ≤ n → K k w) :
    0 ≤ cumValue E V w n :=
  cumValue_nonneg_of_forall_mem E V w n henf
    (fun k hk => by
      exact_mod_cast (calibratedIntensity_pos (hA k hk) (hδ k hk)).le) hq hw

end Workspace.Normativity.Contrib.ProjectionCalibrated

#print axioms Workspace.Normativity.Contrib.ProjectionCalibrated.isNearestPoint_extend
#print axioms Workspace.Normativity.Contrib.ProjectionCalibrated.realizes_extend
#print axioms Workspace.Normativity.Contrib.ProjectionCalibrated.extend_mem_cube
#print axioms Workspace.Normativity.Contrib.ProjectionCalibrated.calibratedIntensity_mul
#print axioms Workspace.Normativity.Contrib.ProjectionCalibrated.dist2_le_of_calibrated
#print axioms Workspace.Normativity.Contrib.ProjectionCalibrated.cumValue_ge_of_calibrated
#print axioms Workspace.Normativity.Contrib.ProjectionCalibrated.cumValue_nonneg_of_calibrated
