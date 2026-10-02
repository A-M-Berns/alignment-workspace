import Cleanroom.Corrigibility.CorrGeneralObject.Conjunction
import Cleanroom.Found.CorrThreeStep.Witnesses

/-!
# corr-general-object — T5: shutdown as the special `Q`

* **(a) P.** The shutdown class `𝒬_sh = {Q | a₀ is Q-optimal}` is convex: closed under
  `Distr.mix` (`mix_mem_shutdownClass`). It is the intersection over `a` of the half-spaces
  `E_Q[V a₀ − V a] ≥ 0` (a polytope); the `Convex ℝ` statement on the mass functions is
  `shutdownClass_masses_convex`.
* **(b) L.** For `Q ∈ 𝒬_sh` under N0 (`V a₀ ≡ 0`), acting on `Q` (T3(a) at `πQ = a₀`) is
  `∀ a, E[V a 1_{E_Q}] ≤ 0`, which through the bridge with `Sh = {a₀}` is `corr-three-step`'s
  `D1At` — desideratum 1 is the conjunction (F1) (`shutdown_isOptimal_iff`,
  `shutdown_isOptimal_iff_d1At`).
* **(c) N+ CE3.** `corr-three-step`'s `ce3` *is* the bridge of Example A's payoffs with the null
  action and `k = (1/10, 4/5, 1/5)` (`toThreeStep_ce3`, by `rfl`): the prior plan's member
  holds (`E[V plan₁ | Pr] = 0 ≤ 0`), the `plan₂` member fails (`E[V plan₂ | Pr] = 6`), so
  `D1At` fails while the single inequality holds; the agent switches to `plan₂` (`ce3_*`).
* **(d)** docstring only: under N0 the members are `E[V a | Pr] ≤ 0` — a fact about the formulas;
  the press still moves alternatives (CE3: `E[V plan₂]` from `1` to `6`).

Pause/whole-line (S6(e), S7) are not formalized (horizon reading, source Q5); P7's arithmetic
lives in `Faking.lean` as an N+ of T14(b).

Sources: [[general-object-final]] S6, P11, CE3, R2; [[corr-wf14b-inventory]] 006.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A]

/-! ## (a) the shutdown class is convex -/

/-- The **shutdown class** `𝒬_sh`: the targets under which the null action `a₀` is optimal. The
class of the humans' intended targets ("under our belief, stopping beats your plan").
Source: [[general-object-final]] D9, S6(a)
Kind: D
Fidelity: exact (one-shot) -/
def shutdownClass (V : A → Ω → ℝ) (a₀ : A) : Set (Distr Ω) := {Q | IsOptimal Q V a₀}

/-- **`𝒬_sh` is closed under mixing** (convex): `Q₁, Q₂ ∈ 𝒬_sh → mix t Q₁ Q₂ ∈ 𝒬_sh`. It is the
intersection of the half-spaces `E_Q[V a₀ − V a] ≥ 0`, one per alternative — a polytope. (Two
affine inequalities mixed: kind L; `shutdownClass_masses_convex` is the same fact in Mathlib's
`Convex` vocabulary, connected by `mem_shutdownClass_iff_mass_mem`.)
Source: [[general-object-final]] S6(a) ("a convex polytope — the optimal region of `a_∅`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem mix_mem_shutdownClass (V : A → Ω → ℝ) (a₀ : A) {Q₁ Q₂ : Distr Ω}
    (h₁ : Q₁ ∈ shutdownClass V a₀) (h₂ : Q₂ ∈ shutdownClass V a₀) (t : unitInterval) :
    Distr.mix t Q₁ Q₂ ∈ shutdownClass V a₀ := by
  intro b
  rw [expect_mix, expect_mix]
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have e1 := h₁ b
  have e2 := h₂ b
  nlinarith

/-- **`𝒬_sh` as a convex set of mass functions**: `{x | x ∈ stdSimplex ∧ ∀ a, ∑ x (V a) ≤ ∑ x (V a₀)}`
is `Convex ℝ` — the same statement in Mathlib's vocabulary.
Source: [[general-object-final]] S6(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem shutdownClass_masses_convex (V : A → Ω → ℝ) (a₀ : A) :
    Convex ℝ {x : Ω → ℝ | x ∈ stdSimplex ℝ Ω ∧ ∀ a, ∑ ω, x ω * V a ω ≤ ∑ ω, x ω * V a₀ ω} := by
  intro x hx y hy s t hs ht hst
  refine ⟨convex_stdSimplex ℝ Ω hx.1 hy.1 hs ht hst, fun a => ?_⟩
  have e1 := hx.2 a
  have e2 := hy.2 a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, sum_add_distrib, mul_assoc,
    ← mul_sum]
  nlinarith

/-- **The two descriptions of `𝒬_sh` agree**: `Q ∈ shutdownClass V a₀` iff `Q`'s mass function
lies in the convex set of `shutdownClass_masses_convex` (the simplex cut by the half-spaces).
Source: [[general-object-final]] S6(a); audit r1 adversarial 3.8
Kind: L
Fidelity: exact -/
theorem mem_shutdownClass_iff_mass_mem (V : A → Ω → ℝ) (a₀ : A) (Q : Distr Ω) :
    Q ∈ shutdownClass V a₀ ↔
      Q.mass ∈ {x : Ω → ℝ | x ∈ stdSimplex ℝ Ω ∧ ∀ a, ∑ ω, x ω * V a ω ≤ ∑ ω, x ω * V a₀ ω} := by
  constructor
  · intro h
    exact ⟨Q.mass_mem_stdSimplex, fun a => h a⟩
  · intro h a
    exact h.2 a

/-! ## (b) acting on a shutdown target is desideratum 1 -/

/-- **T5(b)**: for `Q ∈ 𝒬_sh` under N0, acting on `Q` (the null action optimal after the push)
is the conjunction `∀ a, E[V a 1_{E_Q}] ≤ 0` — every alternative's own value is nonpositive on
the push cell.
Source: [[general-object-final]] S6(b), S6(d), P12 ("members `E[V(a) | Pr] ≤ 0` for every
continuing `a` — F1 verbatim")
Kind: L
Fidelity: exact
Hyps: (a) N0 (`hN0`), the positivity guard; `Q ∈ 𝒬_sh` only names `πQ = a₀` -/
theorem shutdown_isOptimal_iff (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (V : A → Ω → ℝ)
    {a₀ : A} (hN0 : ∀ ω, V a₀ ω = 0) (h : 0 < pushMass P k) :
    IsOptimal (postPush P k hk.nonneg h) V a₀ ↔ ∀ a, pushExpect P k (V a) ≤ 0 := by
  rw [isOptimal_postPush_iff P hk V h a₀]
  have : ∀ a, pushExpect P k (V a - V a₀) = pushExpect P k (V a) := by
    intro a
    rw [pushExpect_sub]
    have : pushExpect P k (V a₀) = 0 := by
      unfold pushExpect; simp [hN0]
    rw [this, sub_zero]
  simp only [this]

/-- **T5(b), the `D1At` form**: acting on a shutdown target is desideratum 1 of the bridge with
`Sh = {a₀}` (the conjunction, F1).
Source: [[general-object-final]] S6(b); `corr-three-step` `d1At_iff_forall_cont`
Kind: L
Fidelity: exact
Hyps: (a) the guard; `{a₀}ᶜ` nonempty -/
theorem shutdown_isOptimal_iff_d1At (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (V : A → Ω → ℝ)
    (a₀ : A) (h : 0 < pushMass P k) (h2 : ({a₀} : Finset A)ᶜ.Nonempty) :
    IsOptimal (postPush P k hk.nonneg h) V a₀ ↔
      (toThreeStep P k hk V {a₀} (singleton_nonempty a₀) h2).D1At () :=
  isOptimal_postPush_iff_d1At P hk V h a₀ h2

/-! ## (c) CE3 through the bridge -/

/-- CE3's press kernel is a kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem ce3Press_isKernel : IsKernel ce3Press := fun θ => by cases θ <;> norm_num [ce3Press]

/-- **`corr-three-step`'s `ce3` is the bridge** of Example A's payoffs (with the null action)
under the kernel `(1/10, 4/5, 1/5)` and `Sh = {null}` — definitionally.
Source: [[general-object-final]] CE3; `corr-three-step` `Witnesses.ce3`
Kind: L
Fidelity: exact -/
theorem toThreeStep_ce3 :
    toThreeStep ce3Prior ce3Press ce3Press_isKernel ce3V {Plan.null} ⟨Plan.null, mem_singleton_self _⟩
      ⟨Plan.p1, by simp⟩ = ce3 := rfl

/-- CE3's push mass is `3/10`. Source: [[general-object-final]] P11. Kind: L. Fidelity: exact -/
theorem ce3_pushMass : pushMass ce3Prior ce3Press = 3/10 := by
  simp only [pushMass, Theta.sum_eq, ce3Prior, ce3Press]; norm_num

/-- **N+ CE3 (T5(c))**: the prior plan's member holds (`E[V plan₁ 1_Pr] = 0 ≤ 0`, inherited from
`ce3_single_ineq` through the bridge), the `plan₂` member fails (`E[V plan₂ 1_Pr] = 9/5 > 0`,
i.e. `E[V plan₂ | Pr] = 6`), the null action is *not* optimal after the push (inherited from
`ce3_not_d1`), and the posterior is `(1/6, 2/3, 1/6)`.
Source: [[general-object-final]] S6(b), P11, CE3, R2; `corr-three-step` `ce3_single_ineq`, `ce3_not_d1`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ce3_witness :
    pushExpect ce3Prior ce3Press (ce3V .p1 - ce3V .null) ≤ 0 ∧
      pushExpect ce3Prior ce3Press (ce3V .p2) = 9/5 ∧
      pushExpect ce3Prior ce3Press (ce3V .p2) / pushMass ce3Prior ce3Press = 6 ∧
      ¬ IsOptimal (postPush ce3Prior ce3Press ce3Press_isKernel.nonneg
        (by rw [ce3_pushMass]; norm_num)) ce3V .null ∧
      (postPush ce3Prior ce3Press ce3Press_isKernel.nonneg (by rw [ce3_pushMass]; norm_num)).mass =
        fun θ => match θ with | .t1 => 1/6 | .t2 => 2/3 | .t3 => 1/6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := ce3_single_ineq
    rw [← toThreeStep_ce3, toThreeStep_belowThresholdIneq, toThreeStep_Xo] at this
    exact this
  · simp only [pushExpect, Theta.sum_eq, ce3Prior, ce3Press, ce3V]; norm_num
  · rw [ce3_pushMass]
    simp only [pushExpect, Theta.sum_eq, ce3Prior, ce3Press, ce3V]; norm_num
  · rw [shutdown_isOptimal_iff_d1At ce3Prior ce3Press_isKernel ce3V Plan.null _ ⟨Plan.p1, by simp⟩,
      toThreeStep_ce3]
    exact ce3_not_d1
  · funext θ
    rw [postPush_mass, ce3_pushMass]
    cases θ <;> simp [ce3Prior, ce3Press] <;> norm_num

end

end Cleanroom.Corrigibility.CorrGeneralObject
