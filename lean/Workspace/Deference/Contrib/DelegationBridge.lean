/-
# The local delegation bridge

Source: `prompts/2026-08-11-deference-finite-kernel/REPORT.md` §1.2 (T1, T1′, T1″),
with the inhabitation witness of that report's §3/§6 certificate `E1`.

The whole file is finite, exact-rational (`AGENTS.md` standard 2), and free of any
Logical-Induction fact. Grade trust `GT_𝒢(η)` enters as a named hypothesis
(`AGENTS.md` standard 4); nothing is asserted as an `axiom`.

**Modelling.** The source states T1 over an admissible conditioning partition `𝒢` of a
finite `Ω`. Here `𝒢` is carried by its cell type `C` directly: a `𝒢`-measurable object
*is* a function on `C`, and `p` is the cell mass. That is the substance of admissibility
— the source's proof uses nothing about `𝒢` except that `J`, `c` and `W(·,π)` are constant
on cells — but it is a re-typing, not a transcription, and the price is that
`𝒢`-measurability is true by construction here rather than a hypothesis to discharge.

Provisional names (`AGENTS.md` §6): `valuation`, `gradeMargin`, `disagreementMass`,
`GradeTrust`, `delegation_bridge`, `delegation_bridge_unconditional`,
`gradeTrust_of_refinement`.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Workspace.Deference.Contrib.DelegationBridge

open Finset

variable {C P : Type*} [Fintype C] [DecidableEq P]

/-- `V_n(c)` of the source's §1.2, with the conditional expectations `E_P[X_π | ·]` taken
as the carrier `EX` and the cell masses as `p`. -/
def valuation (p : C → ℚ) (EX : C → P → ℚ) (sel : C → P) : ℚ :=
  ∑ x, p x * EX x (sel x)

/-- The grade margin `M(c) = E_P[W(·,J) − W(·,c)]` of the source's §1.2. -/
def gradeMargin (p : C → ℚ) (W : C → P → ℚ) (J sel : C → P) : ℚ :=
  ∑ x, p x * (W x (J x) - W x (sel x))

/-- The disagreement mass `D(c) = P({c ≠ J})` of the source's §1.2. -/
def disagreementMass (p : C → ℚ) (J sel : C → P) : ℚ :=
  ∑ x, if sel x ≠ J x then p x else 0

/-- Grade trust at level `η`, `GT_𝒢(η)` of the source's §1.2: on every cell and for every
intervention, the conditional expectation of the quantity is within `η` of the principal's
grade. This is the source's substantive hypothesis and it is imported, not derived — the
source's §1.1 and §4 argue at length that no settlement instantiation in the skeleton
produces it. -/
def GradeTrust (EX W : C → P → ℚ) (η : ℚ) : Prop :=
  ∀ x π, |EX x π - W x π| ≤ η

omit [DecidableEq P] in
/-- `M(c) ≥ 0` whenever `J` is pointwise grade-maximal — the source's "with no hypothesis"
remark in §1.2. -/
theorem gradeMargin_nonneg {p : C → ℚ} {W : C → P → ℚ} {J sel : C → P}
    (hp : ∀ x, 0 ≤ p x) (hJ : ∀ x π, W x π ≤ W x (J x)) :
    0 ≤ gradeMargin p W J sel :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (by linarith [hJ x (sel x)])

/-- **T1, the local delegation bridge.** Source:
`prompts/2026-08-11-deference-finite-kernel/REPORT.md` §1.2.

Under grade trust at level `η`, delegating beats any `𝒢`-measurable comparator by the
principal's own grade margin, less twice the trust level *on the disagreement region only*.

The two uses of `hGT` are the two one-sided ones, which is where the constant `2` comes
from; `hp` is the only other hypothesis. The bound is attained — see `E1` below. -/
theorem delegation_bridge {p : C → ℚ} {EX W : C → P → ℚ} {J sel : C → P} {η : ℚ}
    (hp : ∀ x, 0 ≤ p x) (hGT : GradeTrust EX W η) :
    valuation p EX sel + gradeMargin p W J sel
        - 2 * η * disagreementMass p J sel
      ≤ valuation p EX J := by
  have key : ∀ x ∈ (univ : Finset C),
      p x * EX x (sel x) + p x * (W x (J x) - W x (sel x))
          - 2 * η * (if sel x ≠ J x then p x else 0)
        ≤ p x * EX x (J x) := by
    intro x _
    by_cases hx : sel x = J x
    · rw [hx, if_neg (by simp)]
      ring_nf
      exact le_of_eq rfl
    · rw [if_pos hx]
      have h1 := (abs_le.mp (hGT x (J x))).1
      have h2 := (abs_le.mp (hGT x (sel x))).2
      have step : EX x (sel x) + (W x (J x) - W x (sel x)) - 2 * η ≤ EX x (J x) := by
        linarith
      nlinarith [hp x]
  have := Finset.sum_le_sum key
  simpa [valuation, gradeMargin, disagreementMass, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.mul_sum] using this

/-- **T1′, the unconditional form.** Source: same report, §1.2. With no trust hypothesis at
all, the deficit is at most `2B` on the disagreement region, `B` bounding the quantity. -/
theorem delegation_bridge_unconditional {p : C → ℚ} {EX : C → P → ℚ} {J sel : C → P}
    {B : ℚ} (hp : ∀ x, 0 ≤ p x) (hB : ∀ x π, |EX x π| ≤ B) :
    valuation p EX sel - 2 * B * disagreementMass p J sel ≤ valuation p EX J := by
  have key : ∀ x ∈ (univ : Finset C),
      p x * EX x (sel x) - 2 * B * (if sel x ≠ J x then p x else 0)
        ≤ p x * EX x (J x) := by
    intro x _
    by_cases hx : sel x = J x
    · rw [hx, if_neg (by simp)]
      ring_nf
      exact le_of_eq rfl
    · rw [if_pos hx]
      have h1 := (abs_le.mp (hB x (J x))).1
      have h2 := (abs_le.mp (hB x (sel x))).2
      have step : EX x (sel x) - 2 * B ≤ EX x (J x) := by linarith
      nlinarith [hp x]
  have := Finset.sum_le_sum key
  simpa [valuation, disagreementMass, Finset.sum_sub_distrib, Finset.mul_sum] using this

/-! ## T1″ — the comparator dial

Source: same report, §1.2. Refining the conditioning partition strengthens the trust
hypothesis. The refinement is carried explicitly: `r` sends a fine cell to the coarse cell
containing it, `q` is the conditional mass of the fine cell within it, the coarse
conditional expectation is the `q`-average of the fine ones, and the grade is the same
constant on a coarse cell and each of its fine parts.
-/

/-- The pointwise step of T1″: a convex combination of numbers each within `η` of `w` is
within `η` of `w`. -/
theorem abs_weightedSum_sub_le {ι : Type*} (s : Finset ι) (q f : ι → ℚ) (w η : ℚ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hs : ∑ i ∈ s, q i = 1)
    (h : ∀ i ∈ s, |f i - w| ≤ η) :
    |(∑ i ∈ s, q i * f i) - w| ≤ η := by
  have hrw : (∑ i ∈ s, q i * f i) - w = ∑ i ∈ s, q i * (f i - w) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  rw [hrw]
  calc |∑ i ∈ s, q i * (f i - w)| ≤ ∑ i ∈ s, |q i * (f i - w)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, q i * |f i - w| := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [abs_mul, abs_of_nonneg (hq i hi)]
    _ ≤ ∑ i ∈ s, q i * η :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (hq i hi)
    _ = η := by rw [← Finset.sum_mul, hs, one_mul]

omit [Fintype C] [DecidableEq P] in
/-- **T1″, the comparator dial.** Source: same report, §1.2. `GT` at the finer partition
implies `GT` at the coarser one, at the same level `η`; the source's §1.2 records that the
implication is strict in general (witness W1), which is not formalized here. -/
theorem gradeTrust_of_refinement [DecidableEq C] {Cf : Type*} [Fintype Cf] (r : Cf → C)
    (q : Cf → ℚ) (EXf Wf : Cf → P → ℚ) (EXc Wc : C → P → ℚ) (η : ℚ)
    (hq : ∀ y, 0 ≤ q y)
    (hsum : ∀ x : C, ∑ y ∈ univ.filter (fun y => r y = x), q y = 1)
    (hEX : ∀ (x : C) (π : P), EXc x π = ∑ y ∈ univ.filter (fun y => r y = x), q y * EXf y π)
    (hW : ∀ (y : Cf) (π : P), Wf y π = Wc (r y) π)
    (hfine : GradeTrust EXf Wf η) :
    GradeTrust EXc Wc η := by
  classical
  intro x π
  rw [hEX x π]
  refine abs_weightedSum_sub_le _ q (fun y => EXf y π) (Wc x π) η
    (fun y _ => hq y) (hsum x) ?_
  intro y hy
  have hr : r y = x := (Finset.mem_filter.mp hy).2
  have := hfine y π
  rwa [hW y π, hr] at this

/-! ## `E1` — the inhabitation witness

Source: `prompts/2026-08-11-deference-finite-kernel/REPORT.md` §3 and §6, certificate `E1`,
and `prompts/2026-08-11-deference-finite-kernel/verify.py` (`BASE_W`, `BASE_P`, `ETA`,
`AXES`). Two cells of mass `1/2`; grades `W = ((1, 1/2), (2, 3/2))`, so `J ≡ π₀`;
comparator `c ≡ π₁`; `η = 1/2`. The point of the `E1` box taken here is the corner at which
the report records the bound as attained: `EX = W − η` on the `J`-column and `W + η` on the
comparator column. Every hypothesis of `delegation_bridge` holds, `GT` holds *with equality
at all four coordinates*, and the conclusion holds with equality — so the witness is
neither slack nor degenerate: both cells carry mass, the grade profile is non-constant,
and `D = 1`, `M = 1/2`.
-/

namespace E1

def p : Fin 2 → ℚ := ![1/2, 1/2]
def W : Fin 2 → Fin 2 → ℚ := ![![1, 1/2], ![2, 3/2]]
def EX : Fin 2 → Fin 2 → ℚ := ![![1/2, 1], ![3/2, 2]]
def J : Fin 2 → Fin 2 := ![0, 0]
def c : Fin 2 → Fin 2 := ![1, 1]

theorem p_nonneg : ∀ x, 0 ≤ p x := by
  intro x; fin_cases x <;> norm_num [p]

theorem J_maximal : ∀ x π, W x π ≤ W x (J x) := by
  intro x π; fin_cases x <;> fin_cases π <;> norm_num [W, J]

theorem gradeTrust_half : GradeTrust EX W (1/2) := by
  intro x π; fin_cases x <;> fin_cases π <;> norm_num [EX, W, abs_le]

theorem gradeTrust_attained : ∀ x π, |EX x π - W x π| = 1/2 := by
  intro x π; fin_cases x <;> fin_cases π <;> norm_num [EX, W, abs_sub_comm]

theorem margin_eq : gradeMargin p W J c = 1/2 := by
  norm_num [gradeMargin, p, W, J, c, Fin.sum_univ_two]

theorem disagreement_eq : disagreementMass p J c = 1 := by
  norm_num [disagreementMass, p, J, c, Fin.sum_univ_two]

theorem valuation_J : valuation p EX J = 1 := by
  norm_num [valuation, p, EX, J, Fin.sum_univ_two]

theorem valuation_c : valuation p EX c = 3/2 := by
  norm_num [valuation, p, EX, c, Fin.sum_univ_two]

/-- The bridge instantiated at `E1`, with the bound attained. -/
theorem bridge_at_E1 :
    valuation p EX c + gradeMargin p W J c - 2 * (1/2) * disagreementMass p J c
      = valuation p EX J := by
  rw [margin_eq, disagreement_eq, valuation_J, valuation_c]
  norm_num

/-- The hypothesis package of `delegation_bridge` is inhabited, and the theorem's
conclusion at that inhabitant is the sharp instance above. -/
theorem nonvacuous :
    (∀ x, 0 ≤ p x) ∧ GradeTrust EX W (1/2) ∧
      valuation p EX c + gradeMargin p W J c - 2 * (1/2) * disagreementMass p J c
        ≤ valuation p EX J :=
  ⟨p_nonneg, gradeTrust_half, delegation_bridge p_nonneg gradeTrust_half⟩

end E1

#print axioms gradeMargin_nonneg
#print axioms delegation_bridge
#print axioms delegation_bridge_unconditional
#print axioms abs_weightedSum_sub_le
#print axioms gradeTrust_of_refinement
#print axioms E1.p_nonneg
#print axioms E1.J_maximal
#print axioms E1.gradeTrust_half
#print axioms E1.gradeTrust_attained
#print axioms E1.margin_eq
#print axioms E1.disagreement_eq
#print axioms E1.valuation_J
#print axioms E1.valuation_c
#print axioms E1.bridge_at_E1
#print axioms E1.nonvacuous

end Workspace.Deference.Contrib.DelegationBridge
