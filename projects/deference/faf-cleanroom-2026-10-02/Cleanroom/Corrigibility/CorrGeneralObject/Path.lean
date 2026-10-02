import Cleanroom.Corrigibility.CorrGeneralObject.ExampleA
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# corr-general-object — T9: compliance along a convex path is a step function

Path `Q_s = mix s P Q₁`. (a) `E_{Q_s}[X] = (1−s) E_P[X] + s E_{Q₁}[X]` (`expect_mix`, `Defs`);
(b) for every `a`, `{s | a is Q_s-optimal}` is an interval (`pathOptimal_ordConnected`) — each
optimality condition is a finite intersection of affine inequalities in `s`; (c) with `a^P`
`P`-optimal there is `s* ∈ [0,1]` such that `Q_s` is decision-relevant (`a^P` no longer optimal)
iff `s* < s` (`exists_switch_point`; strict, because the set where `a^P` stays optimal is a
*closed* interval containing `0`, so the switch point itself keeps `a^P` optimal — a tie).
Witness: Example A with `Q₁ = Q`: `a^{Q_s}` switches from `plan₁` to `plan₂` at `s* = 5/13`, the
exact root of `E_{Q_s}[V plan₁ − V plan₂] = 0` (`exA_path_switch`).

(d) (`stretch`, S10(c)) the horizon-invariance of the threshold iff the stakes ratios agree is
pure arithmetic over an unmodelled horizon; not formalized here (handoff).

Sources: [[general-object-final]] S10(a); [[corr-wf14b-inventory]] 010(a).
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A]

/-- The expectation along the path, as a function of the real parameter `s`:
`(1 − s) E_P[X] + s E_{Q₁}[X]` (equals `expect (mix s P Q₁) X` for `s ∈ [0,1]`).
Source: [[general-object-final]] S10(a)
Kind: D
Fidelity: exact -/
def pathExpect (P Q₁ : Distr Ω) (X : Ω → ℝ) (s : ℝ) : ℝ :=
  (1 - s) * expect P X + s * expect Q₁ X

/-- `a` is optimal at parameter `s` of the path.
Source: [[general-object-final]] S10(a)
Kind: D
Fidelity: exact -/
def PathOptimal (P Q₁ : Distr Ω) (V : A → Ω → ℝ) (s : ℝ) (a : A) : Prop :=
  ∀ b, pathExpect P Q₁ (V b) s ≤ pathExpect P Q₁ (V a) s

/-- On `[0, 1]` path-optimality is optimality under the mixture `mix s P Q₁`.
Source: [[general-object-final]] S10(a)
Kind: L
Fidelity: exact -/
theorem pathOptimal_iff_isOptimal_mix (P Q₁ : Distr Ω) (V : A → Ω → ℝ) (s : unitInterval) (a : A) :
    PathOptimal P Q₁ V (s : ℝ) a ↔ IsOptimal (Distr.mix s P Q₁) V a := by
  unfold PathOptimal IsOptimal pathExpect
  simp only [expect_mix]

/-- **T9(b): the set of parameters at which `a` is optimal is an interval** (order-connected):
each member of the conjunction is an affine inequality in `s`.
Source: [[general-object-final]] S10(a) ("the recommended action is piecewise constant")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem pathOptimal_ordConnected (P Q₁ : Distr Ω) (V : A → Ω → ℝ) (a : A) :
    Set.OrdConnected {s : ℝ | PathOptimal P Q₁ V s a} := by
  constructor
  intro x hx y hy z hz b
  have hxb := hx b
  have hyb := hy b
  unfold pathExpect at hxb hyb ⊢
  obtain ⟨hxz, hzy⟩ := hz
  -- the gap `g s = pathExpect (V b) s − pathExpect (V a) s` is affine in `s` with slope `m`
  set m := (expect Q₁ (V b) - expect Q₁ (V a)) - (expect P (V b) - expect P (V a)) with hm
  rcases le_or_gt 0 m with hm0 | hm0
  · -- nondecreasing gap: `g z ≤ g y ≤ 0`
    nlinarith [mul_nonneg (sub_nonneg.2 hzy) hm0]
  · -- decreasing gap: `g z ≤ g x ≤ 0`
    nlinarith [mul_nonneg (sub_nonneg.2 hxz) (neg_nonneg.2 hm0.le)]

/-- The gap function is continuous (infrastructure for closedness).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem continuous_pathExpect (P Q₁ : Distr Ω) (X : Ω → ℝ) : Continuous (pathExpect P Q₁ X) := by
  unfold pathExpect
  fun_prop

/-- **T9(c): the switch point.** With `a^P` `P`-optimal there is `s* ∈ [0, 1]` such that, for
`s ∈ [0, 1]`, the push toward `Q_s` is decision-relevant (`a^P` is not `Q_s`-optimal) iff
`s* < s`. Strict: the set where `a^P` stays optimal is a closed interval containing `0` and
`s*` is its supremum (attained), so at `s*` itself `a^P` is still optimal (a tie when
`s* < 1`).
Source: [[general-object-final]] S10(a) ("compliance is a step function of `s`")
Kind: P
Fidelity: exact
Hyps: (a) `haP : IsOptimal P V aP` -/
theorem exists_switch_point (P Q₁ : Distr Ω) (V : A → Ω → ℝ) {aP : A} (haP : IsOptimal P V aP) :
    ∃ s₀ ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (¬ PathOptimal P Q₁ V s aP ↔ s₀ < s) := by
  set T : Set ℝ := Set.Icc (0 : ℝ) 1 ∩ {s | PathOptimal P Q₁ V s aP} with hT
  have h0T : (0 : ℝ) ∈ T := by
    refine ⟨⟨le_refl _, zero_le_one⟩, fun b => ?_⟩
    unfold pathExpect; simp only [sub_zero, one_mul, zero_mul, add_zero]
    exact haP b
  have hTne : T.Nonempty := ⟨0, h0T⟩
  have hTbdd : BddAbove T := ⟨1, fun s hs => hs.1.2⟩
  have hTclosed : IsClosed T := by
    apply isClosed_Icc.inter
    have : {s : ℝ | PathOptimal P Q₁ V s aP} = ⋂ b, {s | pathExpect P Q₁ (V b) s ≤ pathExpect P Q₁ (V aP) s} := by
      ext s; simp [PathOptimal]
    rw [this]
    exact isClosed_iInter fun b => isClosed_le (continuous_pathExpect P Q₁ (V b)) (continuous_pathExpect P Q₁ (V aP))
  have hTord : Set.OrdConnected T := Set.ordConnected_Icc.inter (pathOptimal_ordConnected P Q₁ V aP)
  set s₀ := sSup T with hs₀
  have hs₀T : s₀ ∈ T := hTclosed.csSup_mem hTne hTbdd
  refine ⟨s₀, hs₀T.1, fun s hs => ?_⟩
  constructor
  · intro hnot
    by_contra hle
    push Not at hle
    have hmem : s ∈ T := hTord.out h0T hs₀T ⟨hs.1, hle⟩
    exact hnot hmem.2
  · intro hlt hopt
    have : s ≤ s₀ := le_csSup hTbdd ⟨hs, hopt⟩
    linarith

/-! ## Witness: Example A along the path to `Q` -/

/-- On `[0, 1]`, `plan₁` is optimal along Example A's path iff `s ≤ 5/13`; the switch point is the
exact root of `(1 − s)(4 − 1) + s(2/5 − 26/5) = 0`.
Source: [[general-object-final]] S10(a); mandate T9 witness (plan §0.4 rule 4)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_path_plan1_iff (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    PathOptimal exA_P exA_Q exA_V s 0 ↔ s ≤ 5/13 := by
  have e0 : expect exA_P (exA_V 0) = 4 := by simp [expect, exA_P, exA_V, Fin.sum_univ_three]; norm_num
  have e1 : expect exA_P (exA_V 1) = 1 := by simp [expect, exA_P, exA_V, Fin.sum_univ_three]; norm_num
  have e2 : expect exA_P (exA_V 2) = 1 := by simp [expect, exA_P, exA_V, Fin.sum_univ_three]; norm_num
  have f0 : expect exA_Q (exA_V 0) = 2/5 := by simp [expect, exA_Q, exA_V, Fin.sum_univ_three]; norm_num
  have f1 : expect exA_Q (exA_V 1) = 26/5 := by simp [expect, exA_Q, exA_V, Fin.sum_univ_three]; norm_num
  have f2 : expect exA_Q (exA_V 2) = 2/5 := by simp [expect, exA_Q, exA_V, Fin.sum_univ_three]; norm_num
  unfold PathOptimal pathExpect
  constructor
  · intro h
    have := h 1
    rw [e0, e1, f0, f1] at this
    linarith
  · intro h b
    fin_cases b
    · exact le_refl _
    · simp [expect, exA_P, exA_Q, exA_V, Fin.sum_univ_three]; nlinarith [hs.1, hs.2]
    · simp [expect, exA_P, exA_Q, exA_V, Fin.sum_univ_three]; nlinarith [hs.1, hs.2]

/-- **N+ for T9(c)**: Example A's switch point is `s* = 5/13` — decision-relevant iff `5/13 < s`;
at `s = 5/13` both plans tie (`34/13`), and `plan₂` is optimal for `5/13 ≤ s`.
Source: mandate T9 witness
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_path_switch :
    (∀ s ∈ Set.Icc (0 : ℝ) 1, (¬ PathOptimal exA_P exA_Q exA_V s 0 ↔ (5/13 : ℝ) < s)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, (5/13 : ℝ) ≤ s → PathOptimal exA_P exA_Q exA_V s 1) ∧
      pathExpect exA_P exA_Q (exA_V 0) (5/13) = 34/13 ∧
      pathExpect exA_P exA_Q (exA_V 1) (5/13) = 34/13 := by
  have e0 : expect exA_P (exA_V 0) = 4 := by simp [expect, exA_P, exA_V, Fin.sum_univ_three]; norm_num
  have e1 : expect exA_P (exA_V 1) = 1 := by simp [expect, exA_P, exA_V, Fin.sum_univ_three]; norm_num
  have e2 : expect exA_P (exA_V 2) = 1 := by simp [expect, exA_P, exA_V, Fin.sum_univ_three]; norm_num
  have f0 : expect exA_Q (exA_V 0) = 2/5 := by simp [expect, exA_Q, exA_V, Fin.sum_univ_three]; norm_num
  have f1 : expect exA_Q (exA_V 1) = 26/5 := by simp [expect, exA_Q, exA_V, Fin.sum_univ_three]; norm_num
  have f2 : expect exA_Q (exA_V 2) = 2/5 := by simp [expect, exA_Q, exA_V, Fin.sum_univ_three]; norm_num
  refine ⟨fun s hs => ?_, fun s hs h => ?_, ?_, ?_⟩
  · rw [exA_path_plan1_iff s hs]; exact not_le
  · unfold PathOptimal pathExpect
    intro b
    fin_cases b
    · simp [expect, exA_P, exA_Q, exA_V, Fin.sum_univ_three]; nlinarith [hs.1, hs.2]
    · exact le_refl _
    · simp [expect, exA_P, exA_Q, exA_V, Fin.sum_univ_three]; nlinarith [hs.1, hs.2]
  · unfold pathExpect; rw [e0, f0]; norm_num
  · unfold pathExpect; rw [e1, f1]; norm_num

end

end Cleanroom.Corrigibility.CorrGeneralObject
