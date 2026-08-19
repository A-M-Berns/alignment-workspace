/-
# The homothetic core: liability without a tolerance penalty

The generic calibrated bound charges `(ρ_n/δ_n)·d₂(w, K_n)` per date, so buying a tighter
tolerance costs liability like `1/δ_n`.  That dependence is an artefact of asking for
nothing but convexity of the region.

There is a geometric condition that removes it.  Say the region `K` has an
**`α`-homothetic core** relative to the live possibility region `P`, anchored at `c ∈ K`,
when `c + α(P − c) ⊆ K` — the region retains an `α`-fraction of the move from `c` toward
every live possibility.  Then the day's liability at any live assessment is at most
`((1−α)/α)·ρ_n`, **with no `δ_n` in it at all**.

The proof is three lines and uses only that a strategy's value is affine in the assessment
point.  Write `x = (1−α)c + αw`.  The core condition puts `x` in `K`, so the projection
trader's value there is nonnegative; affineness splits that value into
`(1−α)Val(c) + αVal(w)`; and the market maker's cube contract caps `Val(c)` by `ρ_n`.
Rearranging gives the bound.

Two things this does **not** say.  It does not bound cumulative liability: a positive core
at every date leaves `Σ_n ((1−α_n)/α_n)ρ_n` free to diverge, and indefinite preservation
still needs a separate summability argument, which `core_cumValue_ge` and
`core_netWorth_ge_of_summable` keep separate on purpose.  And it does not say half-spaces
generally have a core bound depending only on dimension: `α` measures actual geometric
slack against the possibility region, as the two witnesses at the end show.

At `α = 1` the condition says every live possibility is admitted outright and the bound is
zero, which is the deductive case.  So this interpolates continuously between an arbitrary
convex constraint and the zero-liability one.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ProjectionCalibrated

namespace Workspace.Normativity.Contrib.ProjectionCore

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionMarket
open Workspace.Normativity.Contrib.ProjectionBudget
open Workspace.Normativity.Contrib.ProjectionCalibrated

/-! ## The interpolation lemma

No Logical Induction machinery: three real numbers standing for the value at the
interpolated point, at the anchor, and at the assessed point. -/

/-- If an affine value is nonnegative at `(1−α)c + αw`, and at most `ρ` at `c`, then at `w`
it is at least `−((1−α)/α)ρ`. -/
theorem interpolated_lower_bound {α ρ vc vw vx : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hx : 0 ≤ vx) (haffine : vx = (1 - α) * vc + α * vw) (hc : vc ≤ ρ) :
    -((1 - α) / α * ρ) ≤ vw := by
  have hone : (0 : ℝ) ≤ 1 - α := by linarith
  have hstep : 0 ≤ (1 - α) * ρ + α * vw := by
    have : (1 - α) * vc ≤ (1 - α) * ρ := mul_le_mul_of_nonneg_left hc hone
    linarith [hx, haffine.symm ▸ hx]
  have hmul : -((1 - α) * ρ) ≤ α * vw := by linarith
  rw [div_mul_eq_mul_div, ← neg_div, div_le_iff₀ hα0]
  have hswap : α * vw = vw * α := mul_comm α vw
  linarith [hmul, hswap]

/-! ## The value of the projection position is affine in the assessment point -/

lemma ip_interpolate (Φ : Finset Sentence) (ζ p c w : Sentence → ℝ) (α : ℝ) :
    ip Φ ζ (fun φ => ((1 - α) * c φ + α * w φ) - p φ)
      = (1 - α) * ip Φ ζ (fun φ => c φ - p φ)
        + α * ip Φ ζ (fun φ => w φ - p φ) := by
  simp only [ip, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun φ _ => by ring

lemma value_interpolate {Φ : Finset Sentence} {lam : ℝ} {q : Sentence → ℝ} {n : ℕ}
    {T : Strategy n} {V : History} (henf : Realizes Φ lam q T V)
    (c w : Sentence → ℝ) (α : ℝ) :
    T.value V (fun φ => (1 - α) * c φ + α * w φ)
      = (1 - α) * T.value V c + α * T.value V w := by
  rw [henf, henf c, henf w]
  exact ip_interpolate Φ (shares lam (V n) q) (V n) c w α

/-! ## The anchor's value is capped by the day's market resistance

Nothing about the nearest point is used here: any strategy joined into the day's aggregate
has its value at a cube point capped by the market maker's slack plus the rest of the
aggregate's syntactic bound. -/

theorem value_le_resistance (Tr : Trader) (n : ℕ) (ord enf : Strategy n)
    (hjoin : Tr.strat n = Strategy.join [ord, enf]) (c : Sentence → ℝ)
    (hccube : ∀ φ, 0 ≤ c φ ∧ c φ ≤ 1) :
    enf.value (marketMakerHistory Tr) c
      ≤ (marketMakerError n : ℝ) + (ord.absBound : ℝ) := by
  have hcontract := marketMaker_day_value_le_cube Tr n c hccube
  have hsplit : (Tr.strat n).value (marketMakerHistory Tr) c =
      ord.value (marketMakerHistory Tr) c + enf.value (marketMakerHistory Tr) c := by
    rw [hjoin, Strategy.join_value]; simp
  have hord : |ord.value (marketMakerHistory Tr) c| ≤ (ord.absBound : ℝ) :=
    Strategy.abs_value_le ord (marketMakerHistory Tr)
      (fun day φ => marketMakerHistory_mem_Icc Tr day φ) c hccube
  have hordlow := (abs_le.mp hord).1
  rw [hsplit] at hcontract
  linarith

/-! ## The homothetic core -/

/-- `K` retains an `α`-fraction of the move from the anchor `c` toward every point of the
live possibility region `P`.  A per-date geometric condition: nothing relates it across
dates. -/
def HomotheticCore (P K : (Sentence → ℝ) → Prop) (c : Sentence → ℝ) (α : ℝ) : Prop :=
  K c ∧ 0 < α ∧ α ≤ 1 ∧ ∀ w, P w → K (fun φ => (1 - α) * c φ + α * w φ)

/-- At `α = 1` the condition is exactly world-inclusivity of the live region. -/
theorem homotheticCore_one_iff {P K : (Sentence → ℝ) → Prop} {c : Sentence → ℝ}
    (hc : K c) : HomotheticCore P K c 1 ↔ ∀ w, P w → K w := by
  constructor
  · intro h w hw
    have := h.2.2.2 w hw
    simpa using this
  · refine fun h => ⟨hc, one_pos, le_rfl, fun w hw => ?_⟩
    simpa using h w hw

/-- **The homothetic-core liability theorem.**  With an `α`-core relative to the live
possibility region, the day's liability at every live assessment is at most
`((1−α)/α)·ρ_n` — and `δ_n` does not appear. -/
theorem core_day_value_ge
    (Tr : Trader) (n : ℕ) {Φ : Finset Sentence} {K P : (Sentence → ℝ) → Prop}
    {lam α : ℝ} {q c : Sentence → ℝ} (ord enf : Strategy n)
    (hjoin : Tr.strat n = Strategy.join [ord, enf])
    (henf : Realizes Φ lam q enf (marketMakerHistory Tr)) (hlam : 0 ≤ lam)
    (hq : IsNearestPoint Φ K (marketMakerHistory Tr n) q)
    (hcore : HomotheticCore P K c α)
    (hccube : ∀ φ, 0 ≤ c φ ∧ c φ ≤ 1)
    (w : Sentence → ℝ) (hw : P w) :
    -((1 - α) / α * ((marketMakerError n : ℝ) + (ord.absBound : ℝ)))
      ≤ enf.value (marketMakerHistory Tr) w := by
  obtain ⟨hcK, hα0, hα1, hmem⟩ := hcore
  refine interpolated_lower_bound hα0 hα1
    (vx := enf.value (marketMakerHistory Tr) (fun φ => (1 - α) * c φ + α * w φ))
    (day_value_nonneg henf hlam hq _ (hmem w hw))
    (value_interpolate henf c w α)
    (value_le_resistance Tr n ord enf hjoin c hccube)

/-- The calibrated form: the anchor's cube-membership is discharged from the region lying
in the cube on the fragment, via the same extension the calibrated theorems use, and the
charge is stated against market resistance. -/
theorem core_day_value_ge_calibrated
    (Tr : Trader) (n : ℕ) {Φ : Finset Sentence} {K P : (Sentence → ℝ) → Prop}
    {lam α : ℝ} {A : ℚ} {q c : Sentence → ℝ} (ord enf : Strategy n)
    (hjoin : Tr.strat n = Strategy.join [ord, enf])
    (henf : Realizes Φ lam q enf (marketMakerHistory Tr)) (hlam : 0 ≤ lam)
    (hq : IsNearestPoint Φ K (marketMakerHistory Tr n) q)
    (hlocal : FragmentLocal Φ K)
    (hKcube : ∀ y, K y → ∀ φ ∈ Φ, 0 ≤ y φ ∧ y φ ≤ 1)
    (hcore : HomotheticCore P K c α)
    (hA : (ord.absBound : ℚ) ≤ A)
    (w : Sentence → ℝ) (hw : P w) :
    -((1 - α) / α * ((resistance n A : ℚ) : ℝ))
      ≤ enf.value (marketMakerHistory Tr) w := by
  obtain ⟨hcK, hα0, hα1, hmem⟩ := hcore
  set p := marketMakerHistory Tr n with hp
  have hpcube := marketMakerHistory_mem_Icc Tr n
  have hext : ∀ φ, 0 ≤ extend Φ p c φ ∧ extend Φ p c φ ≤ 1 :=
    extend_mem_cube hpcube (fun φ hφ => hKcube c hcK φ hφ)
  have hcoreext : HomotheticCore P K (extend Φ p c) α := by
    refine ⟨hlocal c _ (fun φ hφ => (extend_of_mem hφ).symm) hcK, hα0, hα1, fun y hy => ?_⟩
    refine hlocal _ _ (fun φ hφ => ?_) (hmem y hy)
    simp only [extend_of_mem hφ]
  have hbase := core_day_value_ge Tr n ord enf hjoin henf hlam hq hcoreext hext w hw
  have hcast : ((marketMakerError n : ℝ) + (ord.absBound : ℝ))
      ≤ ((resistance n A : ℚ) : ℝ) := by
    have : ((ord.absBound : ℚ) : ℝ) ≤ ((A : ℚ) : ℝ) := by exact_mod_cast hA
    unfold resistance
    push_cast
    linarith
  have hfac : (0 : ℝ) ≤ (1 - α) / α := div_nonneg (by linarith) hα0.le
  have : (1 - α) / α * ((marketMakerError n : ℝ) + (ord.absBound : ℝ))
      ≤ (1 - α) / α * ((resistance n A : ℚ) : ℝ) :=
    mul_le_mul_of_nonneg_left hcast hfac
  linarith

/-! ## Cumulative

Summing the per-date certificates.  **Positive cores do not by themselves bound the
cumulative liability**: the sum below is free to diverge, and the preservation corollary
takes the uniform bound as a hypothesis rather than deriving it. -/

theorem core_cumValue_ge (E : Trader) (V : History) {ρ α : ℕ → ℝ}
    (w : Sentence → ℝ) (n : ℕ)
    (hday : ∀ k, k ≤ n → -((1 - α k) / α k * ρ k) ≤ (E.strat k).value V w) :
    -(∑ k ∈ Finset.range (n + 1), (1 - α k) / α k * ρ k) ≤ cumValue E V w n :=
  cumValue_ge_of_dayBounds E V w (fun k => (1 - α k) / α k * ρ k) n hday

/-- **Preservation from a uniformly bounded core charge.**  The hypothesis is exactly a
uniform bound on the partial sums; a positive core at every date does not supply it. -/
theorem core_netWorth_ge_of_summable (E : Trader) (V : History) {ρ α : ℕ → ℝ} {B : ℝ}
    (w : Sentence → ℝ)
    (hday : ∀ k, -((1 - α k) / α k * ρ k) ≤ (E.strat k).value V w)
    (hsum : ∀ n, (∑ k ∈ Finset.range (n + 1), (1 - α k) / α k * ρ k) ≤ B) (n : ℕ) :
    -B ≤ cumValue E V w n := by
  have h := core_cumValue_ge E V w n (fun k _ => hday k)
  have := hsum n
  linarith

/-! ## Two witnesses on one priced sentence

They make the qualitative distinction precise: an inequality constraint can retain a
positive amount of every live direction, and an equality constraint cannot. -/

/-- The single priced sentence of the witnesses. -/
def coreAtom : Sentence := .atom 0

/-- The live possibility region: the sentence may take any value in `[0,1]`. -/
def livePoss : (Sentence → ℝ) → Prop := fun w => 0 ≤ w coreAtom ∧ w coreAtom ≤ 1

/-- The half-space constraint `μ(φ) ≥ 1/2`. -/
def halfSpace : (Sentence → ℝ) → Prop := fun y => 1 / 2 ≤ y coreAtom ∧ y coreAtom ≤ 1

/-- The equality constraint `μ(φ) = 1/2`. -/
def equalityRegion : (Sentence → ℝ) → Prop := fun y => y coreAtom = 1 / 2

/-- **`μ(φ) ≥ 1/2` has a `1/2`-core**, anchored at the endpoint `1`.  The resulting per-date
certificate is `Val_w ≥ −ρ_n`, with no dependence on the tolerance. -/
theorem halfSpace_hasCore :
    HomotheticCore livePoss halfSpace (fun _ => 1) (1 / 2) := by
  refine ⟨by norm_num [halfSpace], by norm_num, by norm_num, ?_⟩
  intro w hw
  obtain ⟨hw0, hw1⟩ := hw
  simp only [halfSpace]
  exact ⟨by linarith, by linarith⟩

/-- The charge factor at that core is `1`. -/
theorem halfSpace_core_factor : (1 - (1 : ℝ) / 2) / (1 / 2) = 1 := by norm_num

/-- **`μ(φ) = 1/2` has no positive core.**  The equality collapses the degree of freedom the
half-space retains, so no anchor and no positive fraction satisfy the all-directions
condition against the same live region. -/
theorem equalityRegion_hasNoCore (c : Sentence → ℝ) (α : ℝ) :
    ¬ HomotheticCore livePoss equalityRegion c α := by
  rintro ⟨hc, hα0, -, hmem⟩
  have hone : livePoss (fun _ => 1) := by norm_num [livePoss]
  have h := hmem (fun _ => 1) hone
  simp only [equalityRegion] at hc h
  rw [hc] at h
  have : α = 0 := by linarith
  exact absurd this hα0.ne'

end Workspace.Normativity.Contrib.ProjectionCore

#print axioms Workspace.Normativity.Contrib.ProjectionCore.interpolated_lower_bound
#print axioms Workspace.Normativity.Contrib.ProjectionCore.value_interpolate
#print axioms Workspace.Normativity.Contrib.ProjectionCore.value_le_resistance
#print axioms Workspace.Normativity.Contrib.ProjectionCore.homotheticCore_one_iff
#print axioms Workspace.Normativity.Contrib.ProjectionCore.core_day_value_ge
#print axioms Workspace.Normativity.Contrib.ProjectionCore.core_day_value_ge_calibrated
#print axioms Workspace.Normativity.Contrib.ProjectionCore.core_cumValue_ge
#print axioms Workspace.Normativity.Contrib.ProjectionCore.core_netWorth_ge_of_summable
#print axioms Workspace.Normativity.Contrib.ProjectionCore.halfSpace_hasCore
#print axioms Workspace.Normativity.Contrib.ProjectionCore.equalityRegion_hasNoCore
