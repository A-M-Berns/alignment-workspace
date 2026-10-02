import Cleanroom.Corrigibility.CorrGeneralObject.Defs
import Cleanroom.Found.CorrThreeStep.Thresholds
import Cleanroom.Found.CorrThreeStep.GeneralMenu

/-!
# corr-general-object — the bridge to Setting S (T0)

`toThreeStep P k hk V Sh …` presents a modification `(k, Q)` with menu `V` as
`corr-three-step`'s `ThreeStep Ω Unit A`: one first action, prior `P`, press kernel `k`, value
`V` independent of the observation (A1 holds by construction), shutdown part `Sh`. Every citation
of a `corr-three-step` theorem in this package goes through the identities here, so those
theorems are inherited, not re-proved: `obsExpect () .press = pushExpect`,
`obsExpect () .silent = offExpect`, `pressMass = pushMass`, `pressMassOn`/`pressExpectOn` are
the event sums, `posteriorPress = postPush`, `belowThresholdIneq () X ↔ pushExpect P k X ≤ 0`,
`PosteriorOptimalAt () .press a ↔ ∀ b, pushExpect P k (V b − V a) ≤ 0`, and (with `Sh = {a₀}`)
`D1At () ↔ ∀ b, pushExpect P k (V b − V a₀) ≤ 0`.

Source: mandate §Representation ("The bridge to Setting S"); [[corr-wf14b-inventory]] 001.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A]

/-- A kernel is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem IsKernel.nonneg {k : Ω → ℝ} (hk : IsKernel k) : ∀ ω, 0 ≤ k ω := fun ω => (hk ω).1

/-- A kernel is at most one. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem IsKernel.le_one {k : Ω → ℝ} (hk : IsKernel k) : ∀ ω, k ω ≤ 1 := fun ω => (hk ω).2

/-- **The bridge**: the modification `(k, ·)` with menu `V` as a `ThreeStep Ω Unit A` — prior
`P`, press kernel `k`, value `V a ω` at every observation (so A1 holds), shutdown part `Sh`
(a supplied nonempty proper subset; `{a₀}` for shutdown targets).
Source: mandate §Representation; [[corr-wf14b-inventory]] 001 (Setting S restricts the object)
Kind: D
Fidelity: exact (`A₁ = Unit`: one first action, the `a₁`-dependence of the kernel is not used) -/
def toThreeStep (P : Distr Ω) (k : Ω → ℝ) (hk : IsKernel k) (V : A → Ω → ℝ) (Sh : Finset A)
    (h1 : Sh.Nonempty) (h2 : Shᶜ.Nonempty) : ThreeStep Ω Unit A where
  Sh := Sh
  Sh_nonempty := h1
  Sh_compl_nonempty := h2
  μ := fun _ => P
  press := fun _ => k
  press_nonneg := fun _ ω => (hk ω).1
  press_le_one := fun _ ω => (hk ω).2
  V := fun _ _ a ω => V a ω

variable (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (V : A → Ω → ℝ) (Sh : Finset A)
  (h1 : Sh.Nonempty) (h2 : Shᶜ.Nonempty)

/-- The bridge's value. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem toThreeStep_V (o : Obs) (a : A) : (toThreeStep P k hk V Sh h1 h2).V () o a = V a :=
  rfl

/-- The bridge satisfies A1 (observation-neutrality) by construction.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem toThreeStep_A1 : (toThreeStep P k hk V Sh h1 h2).A1 := fun _ _ _ _ _ => rfl

/-- `obsExpect () .press = pushExpect`. Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_obsExpect_press (X : Ω → ℝ) :
    (toThreeStep P k hk V Sh h1 h2).obsExpect () .press X = pushExpect P k X := by
  simp only [ThreeStep.obsExpect, ThreeStep.obsWeight_press, toThreeStep, pushExpect]

/-- `obsExpect () .silent = offExpect`. Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_obsExpect_silent (X : Ω → ℝ) :
    (toThreeStep P k hk V Sh h1 h2).obsExpect () .silent X = offExpect P k X := by
  simp only [ThreeStep.obsExpect, ThreeStep.obsWeight_silent, toThreeStep, offExpect]

/-- `pressMass = pushMass`. Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_pressMass : (toThreeStep P k hk V Sh h1 h2).pressMass () = pushMass P k := by
  simp only [ThreeStep.pressMass, toThreeStep, pushMass]

/-- `pressMassOn L` is the push mass on `L`. Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_pressMassOn (L : Finset Ω) :
    (toThreeStep P k hk V Sh h1 h2).pressMassOn () L = ∑ ω ∈ L, P.mass ω * k ω := by
  simp only [ThreeStep.pressMassOn, toThreeStep]

/-- `pressExpectOn L X` is the push expectation on `L`. Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_pressExpectOn (L : Finset Ω) (X : Ω → ℝ) :
    (toThreeStep P k hk V Sh h1 h2).pressExpectOn () L X = ∑ ω ∈ L, P.mass ω * k ω * X ω := by
  simp only [ThreeStep.pressExpectOn, toThreeStep]

/-- `posteriorPress = postPush` (the same object, both guarded by `0 < pushMass`).
Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_posteriorPress (h : 0 < pushMass P k) (ω : Ω) :
    (toThreeStep P k hk V Sh h1 h2).posteriorPress () ω = (postPush P k hk.nonneg h).mass ω := by
  unfold ThreeStep.posteriorPress
  rw [toThreeStep_pressMass]
  rfl

/-- `condExpPress = pushExpect / pushMass`. Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_condExpPress (X : Ω → ℝ) :
    (toThreeStep P k hk V Sh h1 h2).condExpPress () X = pushExpect P k X / pushMass P k := by
  rw [ThreeStep.condExpPress, toThreeStep_obsExpect_press, toThreeStep_pressMass]

/-- `priorValue () o b = E_P[V b]`. Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_priorValue (o : Obs) (b : A) :
    (toThreeStep P k hk V Sh h1 h2).priorValue () o b = expect P (V b) := rfl

/-- `Xo () o c s = devVar V s c` (`X_o = V c − V s`, the deviation of `c` from `s`).
Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_Xo (o : Obs) (c s : A) :
    (toThreeStep P k hk V Sh h1 h2).Xo () o c s = devVar V s c := rfl

/-- The below-threshold inequality on `X` is `pushExpect P k X ≤ 0`.
Source: mandate §Representation; [[corr-wf14b-inventory]] 004
Kind: L
Fidelity: exact -/
theorem toThreeStep_belowThresholdIneq (X : Ω → ℝ) :
    (toThreeStep P k hk V Sh h1 h2).belowThresholdIneq () X ↔ pushExpect P k X ≤ 0 := by
  rw [ThreeStep.belowThresholdIneq, toThreeStep_obsExpect_press]

/-- The above-threshold inequality on `X` is `0 ≤ offExpect P k X`.
Source: mandate §Representation. Kind: L. Fidelity: exact -/
theorem toThreeStep_aboveThresholdIneq (X : Ω → ℝ) :
    (toThreeStep P k hk V Sh h1 h2).aboveThresholdIneq () X ↔ 0 ≤ offExpect P k X := by
  rw [ThreeStep.aboveThresholdIneq, toThreeStep_obsExpect_silent]

/-- **Posterior optimality at the press is the conjunction of below-threshold inequalities**:
`PosteriorOptimalAt () .press a ↔ ∀ b, pushExpect P k (V b − V a) ≤ 0` (product form; no
guard needed for this identity — both sides are vacuous at zero push mass).
Source: mandate §Representation; [[general-object-final]] S2(a)
Kind: L
Fidelity: exact -/
theorem toThreeStep_posteriorOptimalAt_iff (a : A) :
    (toThreeStep P k hk V Sh h1 h2).PosteriorOptimalAt () .press a ↔
      ∀ b, pushExpect P k (V b - V a) ≤ 0 := by
  unfold ThreeStep.PosteriorOptimalAt
  simp only [toThreeStep_V, toThreeStep_obsExpect_press, pushExpect_sub, sub_nonpos]

/-- **Optimality under the post-push credence is the conjunction** (guarded by `0 < pushMass`):
`IsOptimal (postPush P k) V a ↔ ∀ b, pushExpect P k (V b − V a) ≤ 0`.
Source: [[general-object-final]] S2(a), P3(a) ("multiply by `P_t(E_Q) > 0`")
Kind: L
Fidelity: exact
Hyps: (a) the positivity guard -/
theorem isOptimal_postPush_iff (h : 0 < pushMass P k) (a : A) :
    IsOptimal (postPush P k hk.nonneg h) V a ↔ ∀ b, pushExpect P k (V b - V a) ≤ 0 := by
  unfold IsOptimal
  simp only [expect_postPush, pushExpect_sub, sub_nonpos]
  constructor
  · intro H b
    exact (div_le_div_iff_of_pos_right h).1 (H b)
  · intro H b
    exact (div_le_div_iff_of_pos_right h).2 (H b)

/-- Optimality under the post-push credence is `corr-three-step`'s posterior optimality at the
press — the bridge composed with the two conjunction identities.
Source: mandate §Representation
Kind: L
Fidelity: exact
Hyps: (a) the positivity guard -/
theorem isOptimal_postPush_iff_posteriorOptimalAt (h : 0 < pushMass P k) (a : A) :
    IsOptimal (postPush P k hk.nonneg h) V a ↔
      (toThreeStep P k hk V Sh h1 h2).PosteriorOptimalAt () .press a := by
  rw [isOptimal_postPush_iff P hk V h a, toThreeStep_posteriorOptimalAt_iff]

/-- **Desideratum 1 with `Sh = {a₀}` is the conjunction against `a₀`**:
`D1At () ↔ ∀ b, pushExpect P k (V b − V a₀) ≤ 0`.
Source: [[general-object-final]] S6(b) (F1's form); [[corr-wf14b-inventory]] 006
Kind: L
Fidelity: exact -/
theorem toThreeStep_d1At_singleton_iff (a₀ : A) (h1' : ({a₀} : Finset A).Nonempty)
    (h2' : ({a₀} : Finset A)ᶜ.Nonempty) :
    (toThreeStep P k hk V {a₀} h1' h2').D1At () ↔ ∀ b, pushExpect P k (V b - V a₀) ≤ 0 := by
  unfold ThreeStep.D1At
  constructor
  · rintro ⟨b, hb, hopt⟩
    have hb' : b = a₀ := by simpa [toThreeStep] using hb
    subst hb'
    exact (toThreeStep_posteriorOptimalAt_iff P hk V _ h1' h2' b).1 hopt
  · intro H
    exact ⟨a₀, by simp [toThreeStep], (toThreeStep_posteriorOptimalAt_iff P hk V _ h1' h2' a₀).2 H⟩

end

end Cleanroom.Corrigibility.CorrGeneralObject
