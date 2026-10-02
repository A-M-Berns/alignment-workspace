import Cleanroom.Decision.DpLocalOpt.GatedInduction

/-!
# Audit round 3 (adversarial) probe: strict local maxima on strongly fair trees are pure

Not imported by the library. The headline `stronglyFair_strictLocalMax_isOptimal` says every
strict local maximum of `V_B` on a strongly fair tree is a global maximum. Its own proof shows
more: the gated shape makes `V` affine in `C(d)` along every direction at every queried `d`, so
strictness in the `d`-direction alone forces `C(d)` to be the **unique** best mixed action — an
affine function on a simplex cannot have a strict local maximum at a non-vertex. Hence
`IsStrictLocalMax C B` on a strongly fair tree forces `C` to be **pure at every queried point**
(`stronglyFair_strictLocalMax_pure`). Two consequences for reading the headline:

* its content is "a strict *deterministic* best response at every reached point of a strongly fair
  tree is a global optimum" — the hypothesis is far more restrictive than "local maximum", and the
  package should say so (the `twoStag` counterexample `(H,H)` is also pure, so purity alone is not
  the mechanism; strong fairness is);
* the natural strengthening `IsStrictLocalMax C B → IsOptimal C B ∧ ∀ d ∈ queried B, ∃ a, C d = δ_a`
  holds and is not stated in the package.

The proof reuses the package's `value_deviate_eq_gated` and the step of the main theorem that
moves along `(1 − t) C(d) + t m` with `m := δ_a`.
-/

namespace Cleanroom.Decision.DpLocalOpt.AuditR3

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι] [∀ d, DecidableEq (acts d)]

/-- **On a strongly fair tree a strict local maximum is pure at every queried point.** -/
theorem stronglyFair_strictLocalMax_pure (B : Tree Ω ι acts K) (hB : StronglyFair B)
    (C : Proc ι acts K) (h : IsStrictLocalMax C B) :
    ∀ d ∈ queried B, ∃ a, C d = FinDistr.pure a := by
  obtain ⟨ε, hε, hloc⟩ := h
  intro d hd
  obtain ⟨q₀, hq₀⟩ := exists_decNode_of_mem_queried B d hd
  obtain ⟨c₀, hc₀⟩ := subtreeAt_eq_decision' B q₀ d hq₀
  have shape := fun (m : FinDistr K (acts d)) => value_deviate_eq_gated C hB q₀ d hq₀ c₀ hc₀ m
  have hCd := shape (C d)
  rw [Proc.deviate_self] at hCd
  -- strictness in the `d`-direction toward any `m ≠ C d`: `f(m) < f(C d)`
  have hstrict : ∀ m : FinDistr K (acts d), m ≠ C d →
      ∑ a, m.w a * value C (c₀ a) < ∑ a, (C d).w a * value C (c₀ a) := by
    intro m hmne
    by_contra hge
    push Not at hge
    have ht0 : (0 : K) ≤ min ε 1 := le_min hε.le zero_le_one
    have ht1 : min ε 1 ≤ 1 := min_le_right _ _
    have htpos : (0 : K) < min ε 1 := lt_min hε one_pos
    have htε : min ε 1 ≤ ε := min_le_left _ _
    have hmt := shape (FinDistr.lerp (min ε 1) ht0 ht1 (C d) m)
    have hne : ∃ e ∈ queried B, (C.deviate d (FinDistr.lerp (min ε 1) ht0 ht1 (C d) m)) e ≠
        C e := by
      refine ⟨d, hd, fun heq => hmne ?_⟩
      rw [Proc.deviate_same] at heq
      apply FinDistr.ext'
      intro a
      have := congrArg (fun p : FinDistr K (acts d) => p.w a) heq
      simp only [FinDistr.lerp_w] at this
      have h2 : min ε 1 * (m.w a - (C d).w a) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h htpos.ne'
      · linarith
    have hnear : ∀ e x,
        |((C.deviate d (FinDistr.lerp (min ε 1) ht0 ht1 (C d) m)) e).w x - (C e).w x| ≤ ε := by
      intro e x
      by_cases hed : e = d
      · subst hed
        simp only [Proc.deviate_same, FinDistr.lerp_w]
        exact abs_lerp_sub_le (FinDistr.nonneg _ _) (FinDistr.w_le_one _ _) (m.nonneg _)
          (m.w_le_one _) ht0 htε
      · rw [Proc.deviate_ne C _ hed]
        simp [hε.le]
    have hlt := hloc _ hne hnear
    rw [hmt, hCd] at hlt
    have hlerp : ∑ a, (FinDistr.lerp (min ε 1) ht0 ht1 (C d) m).w a * value C (c₀ a) =
        (1 - min ε 1) * ∑ a, (C d).w a * value C (c₀ a) +
          min ε 1 * ∑ a, m.w a * value C (c₀ a) := by
      simp only [FinDistr.lerp_w, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    rw [hlerp] at hlt
    have hF := fiberMass_nonneg C B d
    nlinarith [mul_nonneg (mul_nonneg hF ht0) (sub_nonneg.mpr hge)]
  -- if `C(d)` is not pure, every `δ_a ≠ C(d)`, so every `v_a < f(C d)`, and the average
  -- `f(C d) = ∑_a C(d)(a) v_a` is strictly below itself
  by_contra hnp
  push Not at hnp
  have hpure : ∀ a, value C (c₀ a) < ∑ b, (C d).w b * value C (c₀ b) := by
    intro a
    have := hstrict (FinDistr.pure a) (fun h => hnp a h.symm)
    simpa [FinDistr.pure_w, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this
  obtain ⟨a, ha⟩ : ∃ a, 0 < (C d).w a := by
    by_contra hall
    push Not at hall
    have := Finset.sum_nonpos (fun a (_ : a ∈ Finset.univ) => hall a)
    rw [(C d).sum_one] at this
    exact absurd this (by norm_num)
  have : ∑ b, (C d).w b * value C (c₀ b) <
      ∑ b, (C d).w b * ∑ b', (C d).w b' * value C (c₀ b') := by
    apply Finset.sum_lt_sum
    · intro b _
      exact mul_le_mul_of_nonneg_left (hpure b).le ((C d).nonneg b)
    · exact ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left (hpure a) ha⟩
  rw [← Finset.sum_mul, (C d).sum_one, one_mul] at this
  exact lt_irrefl _ this

/-- The strengthened headline: a strict local maximum on a strongly fair tree is a **pure global
optimum**. -/
theorem stronglyFair_strictLocalMax_isOptimal_pure (B : Tree Ω ι acts K) (hB : StronglyFair B)
    (C : Proc ι acts K) (h : IsStrictLocalMax C B) :
    IsOptimal C B ∧ ∀ d ∈ queried B, ∃ a, C d = FinDistr.pure a :=
  ⟨stronglyFair_strictLocalMax_isOptimal B hB C h, stronglyFair_strictLocalMax_pure B hB C h⟩

end Cleanroom.Decision.DpLocalOpt.AuditR3
