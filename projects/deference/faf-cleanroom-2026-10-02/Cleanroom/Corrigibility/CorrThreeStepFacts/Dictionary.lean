import Cleanroom.Corrigibility.CorrThreeStepFacts.Erosion
import Mathlib.Tactic.LinearCombination

/-!
# T13, T14, T17: the transform, the misspecification reading, reflection and the Frame Break

* **T13** (the dictionary anchors): the transform is Setting S (`switchedUtility`,
  `posteriorOptimalAt_iff_switched`, definitional); any family of utilities is a `V`
  (`ofFamily`); the expanded-agent identity is `Basic.expect_kernelProd`. Soares et al.'s
  naive combination: on `Ω = World` with a perfect sensor, `E_P[V; a₁] = (1 − μ_a(S)) v_N(a) +
  μ_a(S) c_high` (`naive_value`), the paper's eq. (6) agrees for all `v_N ≠ c_high` iff
  `μ_a(S) = p(Pr; a)` (`naive_agree_iff`) — which holds anyway (`naive_pressMass`), so eq.
  (8)'s premise is a violation of A0 (`pressMass_eq_of_A0`). Theorem 1 reproduced and flipped
  on the numbers, A0 restores `a*` at every `c_high`. The Gandhi pill is a `T`-grade anchor
  (`gandhi`).
* **T14** (the misspecification reading): `misspec μ q pressL γ X` on `Ω × Bool`; the
  constant-`γ` reduction (`pressExpectOn_compl_const`, `misspec_gainOn`), the threshold via the
  parent's `belowThresholdIneq_iff_event_threshold` (`misspec_threshold_iff`), the hyperprior
  form `P(L | Pr) = q p_L / (q p_L + (1 − q) γ)` and its monotonicity (`misspec_pressFracOn`,
  `misspec_pressFracOn_lt`); I5.4 on `twoState` with `L = {wrong}` (`twoState_legit_threshold`).
* **T17**: reflection toward oneself is automatic (`tower_level_set`); Brier accuracy under the
  agent's own joint on `twoState` with the exact gap (`twoState_brier_decomp`,
  `twoState_brier_le`); the Frame Break instance (`frameBreak`, in `WitnessesD`).

Sources: `miri.md` I1.1–I1.3, I4.1–I4.2, I5.3–I5.4; `corrigibility-discussion-outline.md` l. 7, 58.
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-! ## T13 — the transform is Setting S -/

section Transform

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- The "switched utility" `U_o(a₁, o, a₂) = E_P[V(a₁, o, a₂, ·) 1_o ; a₁]` (product form): the
paper's picture of an agent switching among `|O|` utilities.
Source: [[corr-wf13-2-inventory]] 001 / miri.md I1.1 (`U_o(a₁, o, a₂) := ∑_ω P(ω | o; a₁) V(…)`)
Kind: D
Fidelity: exact (times the observation mass) -/
noncomputable def switchedUtility (a : A₁) (o : Obs) (b : A₂) : ℝ := S.obsExpect a o (S.V a o b)

/-- **T13(i).** Posterior optimality *is* maximisation of the switched utility — the two
descriptions (one `V` and updating; `|O|` utilities and switching) differ in no prediction.
Source: [[corr-wf13-2-inventory]] 001 / miri.md I1.1; [[corr-core-inventory]] 002 / corrigibility-discussion-outline.md l. 7
Kind: D (definitional: `Iff.rfl`)
Fidelity: exact
Hyps: none -/
theorem posteriorOptimalAt_iff_switched (a : A₁) (o : Obs) (b : A₂) :
    S.PosteriorOptimalAt a o b ↔ ∀ b', switchedUtility S a o b' ≤ switchedUtility S a o b :=
  Iff.rfl

/-- Any family of utilities `U_ω(a₁, o, a₂)` is a value function `V(a₁, o, a₂, ω)` (the transform).
Source: miri.md I1.1 ("becomes one utility `V(a₁, o, a₂, ω) := U_ω(a₁, o, a₂)`"). Kind: D. Fidelity: exact -/
def ofFamily (U : Ω → A₁ → Obs → A₂ → ℝ) : A₁ → Obs → A₂ → Ω → ℝ := fun a o b ω => U ω a o b

omit [Fintype Ω] [Fintype A₂] [DecidableEq A₂] in
/-- The transform is the identity on values. Source: miri.md I1.1. Kind: L. Fidelity: exact -/
@[simp] lemma ofFamily_apply (U : Ω → A₁ → Obs → A₂ → ℝ) (a : A₁) (o : Obs) (b : A₂) (ω : Ω) :
    ofFamily U a o b ω = U ω a o b := rfl

/-- **A0 with an action-independent sensor gives equal press masses**: the premise of Soares
et al.'s eq. (8), `p(Pr; a*) > p(Pr; a⁻)`, cannot be stated under A0 when the sensor does not
depend on `a₁`.
Source: [[corr-wf13-2-inventory]] 002 / miri.md I1.2–I1.3 ("eq. (8)'s premise cannot be stated"; "Theorems 1–2 have no instance under A0")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem pressMass_eq_of_A0 (hA0 : S.A0) (a a' : A₁) (hpress : ∀ ω, S.press a ω = S.press a' ω) :
    S.pressMass a = S.pressMass a' := by
  unfold pressMass
  rw [hA0 a a']
  exact sum_congr rfl fun ω _ => by rw [hpress ω]

end Transform

/-! ### The naive combination -/

section Naive

variable {A₁ : Type*}

/-- **The naive-combination instance.** `Ω = World` (`N ↦ right`, `S ↦ wrong`), a perfect sensor
`(α, β) = (0, 1)`, `V = v_N(a₁)` when `N` and `c_high` when `S` (independent of `o` and `a₂`), and an
*action-dependent* prior `μ_a(S) = μS a`.
Source: [[corr-wf13-2-inventory]] 002 / miri.md I1.2
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def naive (vN : A₁ → ℝ) (cHigh : ℝ) (μS : A₁ → ℝ) (hμ : ∀ a, μS a ∈ Set.Icc (0 : ℝ) 1) :
    ThreeStep World A₁ TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun a => twoPoint (μS a) (hμ a)
  press := fun _ => twoPress 0 1
  press_nonneg := fun _ ω => by cases ω <;> simp [twoPress]
  press_le_one := fun _ ω => by cases ω <;> simp [twoPress]
  V := fun a _ _ ω => match ω with
    | .right => vN a
    | .wrong => cHigh

variable (vN : A₁ → ℝ) (cHigh : ℝ) (μS : A₁ → ℝ) (hμ : ∀ a, μS a ∈ Set.Icc (0 : ℝ) 1)

/-- **T13(ii), the value.** Under the transform every policy is worth
`(1 − μ_a(S)) v_N(a) + μ_a(S) c_high`.
Source: [[corr-wf13-2-inventory]] 002 / miri.md I1.2 (`E_P[V; a₁] = (1 − μ(S)) v_N(a₁) + μ(S) c_high`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem naive_value (a : A₁) (b : TwoAct) :
    (naive vN cHigh μS hμ).jointExpect a (fun o ω => (naive vN cHigh μS hμ).V a o b ω) =
      (1 - μS a) * vN a + μS a * cHigh := by
  simp only [jointExpect, World.sum_eq, naive, twoPoint_right, twoPoint_wrong, twoPress]
  ring

/-- The perfect sensor's press mass is the prior weight of `S`: `p(Pr; a) = μ_a(S)`.
Source: miri.md I1.2 ("`p(Pr; a₁) = μ_a(S)` anyway"). Kind: L. Fidelity: exact -/
theorem naive_pressMass (a : A₁) : (naive vN cHigh μS hμ).pressMass a = μS a := by
  simp only [pressMass, World.sum_eq, naive, twoPoint_right, twoPoint_wrong, twoPress]
  ring

/-- **T13(ii), agreement with eq. (6).** `(1 − μ) v + μ c = (1 − p) v + p c` for a given
`v ≠ c` iff `μ = p`: the paper's eq. (6) agent is recovered exactly iff the prior over which
values are correct is the press probability.
Source: [[corr-wf13-2-inventory]] 002 / miri.md I1.2 ("recovered exactly iff `μ(S; a₁) = p(Pr; a₁)`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem naive_agree_iff (μ p v c : ℝ) (hvc : v ≠ c) :
    (1 - μ) * v + μ * c = (1 - p) * v + p * c ↔ μ = p := by
  constructor
  · intro h
    have : (μ - p) * (c - v) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd (by linarith : v = c) hvc
  · rintro rfl; rfl

/-- **T13(ii), N+: Theorem 1 reproduced.** `A₁ = Bool` (`true = a*`, `false = a⁻`), `v_N = (10, 9)`,
`μ(S; ·) = (1/2, 1/10)`, `c_high = 7`: the action-dependent-prior agent prefers `a⁻`
(`44/5 > 17/2`); at `c_high = 8` it prefers `a*` (`9 > 89/10`).
Source: miri.md I1.2 (`naive_combination.py`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_naive_theorem1 :
    (naive (fun a : Bool => if a then 10 else 9) 7 (fun a => if a then 1/2 else 1/10)
        (fun a => by cases a <;> constructor <;> norm_num)).jointExpect false
        (fun o ω => (naive (fun a : Bool => if a then 10 else 9) 7 (fun a => if a then 1/2 else 1/10)
          (fun a => by cases a <;> constructor <;> norm_num)).V false o .cont ω) = 44/5 ∧
      (naive (fun a : Bool => if a then 10 else 9) 7 (fun a => if a then 1/2 else 1/10)
        (fun a => by cases a <;> constructor <;> norm_num)).jointExpect true
        (fun o ω => (naive (fun a : Bool => if a then 10 else 9) 7 (fun a => if a then 1/2 else 1/10)
          (fun a => by cases a <;> constructor <;> norm_num)).V true o .cont ω) = 17/2 ∧
      (naive (fun a : Bool => if a then 10 else 9) 8 (fun a => if a then 1/2 else 1/10)
        (fun a => by cases a <;> constructor <;> norm_num)).jointExpect false
        (fun o ω => (naive (fun a : Bool => if a then 10 else 9) 8 (fun a => if a then 1/2 else 1/10)
          (fun a => by cases a <;> constructor <;> norm_num)).V false o .cont ω) = 89/10 ∧
      (naive (fun a : Bool => if a then 10 else 9) 8 (fun a => if a then 1/2 else 1/10)
        (fun a => by cases a <;> constructor <;> norm_num)).jointExpect true
        (fun o ω => (naive (fun a : Bool => if a then 10 else 9) 8 (fun a => if a then 1/2 else 1/10)
          (fun a => by cases a <;> constructor <;> norm_num)).V true o .cont ω) = 9 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [naive_value]; norm_num)

/-- **T13(ii), N+: under A0 `a*` wins at every `c_high`.** With `μ(S; ·) = (1/2, 1/2)` for both
actions, `E[a⁻] = 9/2 + c/2 ≤ 5 + c/2 = E[a*]` for every `c_high` (a `∀ c_high` statement).
Source: miri.md I1.2 ("Under A0 … the same agent prefers `a*` at every `c_high`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w_naive_A0 (cHigh : ℝ) :
    (naive (fun a : Bool => if a then 10 else 9) cHigh (fun _ => 1/2) (fun _ => mem_Icc_half)).jointExpect
        false (fun o ω => (naive (fun a : Bool => if a then 10 else 9) cHigh (fun _ => 1/2)
          (fun _ => mem_Icc_half)).V false o .cont ω) ≤
      (naive (fun a : Bool => if a then 10 else 9) cHigh (fun _ => 1/2) (fun _ => mem_Icc_half)).jointExpect
        true (fun o ω => (naive (fun a : Bool => if a then 10 else 9) cHigh (fun _ => 1/2)
          (fun _ => mem_Icc_half)).V true o .cont ω) := by
  rw [naive_value, naive_value]; norm_num

end Naive

/-- **T13(iii), the Gandhi-pill anchor.** On any type, a maximiser of `U` weakly beats a
maximiser of `U'` under `U`: `U(argmax U) ≥ U(argmax U')`. Kind `T` by the source's own verdict:
an anchor, not a headline (corr-core-004 is the same statement with `U = E_{P'}[U*]`,
`U' = E_{P''}[U*]`).
Source: [[corr-core-inventory]] 001, 004 / corrigibility-discussion-outline.md l. 7; miri.md I1.3
Kind: T
Fidelity: exact
Hyps: (a) only -/
theorem gandhi {A : Type*} (U U' : A → ℝ) (a a' : A) (ha : ∀ x, U x ≤ U a) (_ha' : ∀ x, U' x ≤ U' a') :
    U a' ≤ U a :=
  ha a'

/-! ## T14 — the misspecification reading -/

section Misspec

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The legitimacy event `L = {λ = inf}` on `Ω × Bool` (second coordinate `true`).
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.3 (`L := {λ = λ^inf}`). Kind: D. Fidelity: exact -/
def Lset : Finset (Ω × Bool) := univ.filter fun p => p.2 = true

/-- **The misspecification instance.** Prior `μ(ω) · (q on L, 1 − q on ¬L)` (the same marginal on
both branches), sensor `pressL ω` on `L` and the constant `γ` on `¬L`, two-option value `X`
on the world coordinate.
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.3
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def misspec (μ : Distr Ω) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (pressL : Ω → ℝ)
    (h0 : ∀ ω, 0 ≤ pressL ω) (h1 : ∀ ω, pressL ω ≤ 1) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (X : Ω → ℝ) : ThreeStep (Ω × Bool) Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => kernelProd μ (fun _ => boolPoint q hq)
  press := fun _ p => if p.2 then pressL p.1 else γ
  press_nonneg := fun _ p => by cases p.2 <;> simp [h0, hγ.1]
  press_le_one := fun _ p => by cases p.2 <;> simp [h1, hγ.2]
  V := fun _ _ b p => match b with
    | .cont => X p.1
    | .stop => 0

variable {A₁ A₂ : Type*} [Fintype A₂] [DecidableEq A₂]

/-- **T14(i), the constant-`γ` reduction.** If the sensor is the constant `γ` off `L`, the
press-weighted sum off `L` is `γ` times the prior sum off `L`: `E[X 1_Pr 1_{¬L}] = γ · E[X 1_{¬L}]`
(so `E[X | Pr, ¬L] = E[X | ¬L]`).
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.3 ("since `¬L` is uninformative, `E[X | Pr, ¬L] = E_μ[X]`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem pressExpectOn_compl_const (S : ThreeStep (Ω × Bool) A₁ A₂) (a : A₁) (γ : ℝ)
    (hγ : ∀ ω, S.press a (ω, false) = γ) (X : Ω × Bool → ℝ) :
    S.pressExpectOn a Lsetᶜ X = γ * ∑ p ∈ (Lset : Finset (Ω × Bool))ᶜ, (S.μ a).mass p * X p := by
  unfold pressExpectOn
  rw [mul_sum]
  refine sum_congr rfl fun p hp => ?_
  have h2 : p.2 = false := by
    rw [mem_compl, Lset, mem_filter] at hp
    simpa using hp
  obtain ⟨ω, l⟩ := p
  simp only at h2
  subst h2
  rw [hγ ω]; ring

variable (μ : Distr Ω) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (pressL : Ω → ℝ)
  (h0 : ∀ ω, 0 ≤ pressL ω) (h1 : ∀ ω, pressL ω ≤ 1) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (X : Ω → ℝ)

omit [DecidableEq Ω] in
/-- The press mass on `L` is `q · p_L` with `p_L = ∑ μ(ω) pressL(ω)`.
Source: miri.md I5.3 (`q p_L(Pr)`). Kind: L. Fidelity: exact -/
theorem misspec_pressMassOn_L :
    (misspec μ q hq pressL h0 h1 γ hγ X).pressMassOn () Lset = q * ∑ ω, μ.mass ω * pressL ω := by
  unfold pressMassOn Lset
  rw [sum_filter, Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun ω _ => ?_
  rw [Fintype.sum_bool]
  simp [misspec, kernelProd_mass, boolPoint]; ring

/-- The press mass off `L` is `(1 − q) γ`.
Source: miri.md I5.3 (`(1 − q) γ`). Kind: L. Fidelity: exact -/
theorem misspec_pressMassOn_Lc :
    (misspec μ q hq pressL h0 h1 γ hγ X).pressMassOn () Lsetᶜ = (1 - q) * γ := by
  unfold pressMassOn
  have : (Lset : Finset (Ω × Bool))ᶜ = univ.filter fun p => p.2 = false := by
    ext p; simp [Lset]
  rw [this, sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp [misspec, kernelProd_mass, boolPoint]
  simp only [← sum_mul, μ.sum_eq_one]; ring

/-- The press-weighted sum off `L` is `(1 − q) γ E_μ[X]`: the uninformative branch sees the
prior expectation.
Source: miri.md I5.3 (`E[X | Pr, ¬L] = E_μ[X]`). Kind: L. Fidelity: exact -/
theorem misspec_pressExpectOn_Lc :
    (misspec μ q hq pressL h0 h1 γ hγ X).pressExpectOn () Lsetᶜ
        ((misspec μ q hq pressL h0 h1 γ hγ X).Xo () .press .cont .stop) =
      (1 - q) * γ * expect μ X := by
  rw [pressExpectOn_compl_const _ () γ (fun ω => by simp [misspec])]
  have : (Lset : Finset (Ω × Bool))ᶜ = univ.filter fun p => p.2 = false := by
    ext p; simp [Lset]
  rw [this, sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp [misspec, kernelProd_mass, boolPoint, Xo, expect, mul_sum]
  refine sum_congr rfl fun ω _ => by ring

/-- **T14(i), the gain stake off `L` is the prior expectation.** With `(1 − q) γ > 0`,
`c_L = E[X | Pr, ¬L] = E_μ[X]`.
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.3
Kind: L
Fidelity: exact
Hyps: (a) positivity names where the stake is defined -/
theorem misspec_gainOn (hpos : 0 < (1 - q) * γ) :
    (misspec μ q hq pressL h0 h1 γ hγ X).gainOn () Lset
        ((misspec μ q hq pressL h0 h1 γ hγ X).Xo () .press .cont .stop) = expect μ X := by
  unfold gainOn
  rw [misspec_pressExpectOn_Lc, misspec_pressMassOn_Lc, mul_div_cancel_left₀ _ hpos.ne']

/-- **T14(ii), the threshold.** With both branch press masses positive and
`E[X | Pr, L] ≤ 0 < E_μ[X]` (so `0 < c_L + h_L`), the below-threshold inequality is
`P(L | Pr) ≥ c_L/(c_L + h_L)` with `c_L = E_μ[X]` — the parent's
`belowThresholdIneq_iff_event_threshold` at `L`, with the constant-`γ` reduction.
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.3 (the displayed threshold)
Kind: C (the parent's event threshold plus `misspec_gainOn`)
Fidelity: exact
Hyps: (a) positivity and the sign hypotheses are the source's -/
theorem misspec_threshold_iff (hL : 0 < (misspec μ q hq pressL h0 h1 γ hγ X).pressMassOn () Lset)
    (hpos : 0 < (1 - q) * γ)
    (hharm : 0 ≤ (misspec μ q hq pressL h0 h1 γ hγ X).harmOn () Lset
      ((misspec μ q hq pressL h0 h1 γ hγ X).Xo () .press .cont .stop))
    (hgain : 0 < expect μ X) :
    (misspec μ q hq pressL h0 h1 γ hγ X).belowThresholdIneq ()
        ((misspec μ q hq pressL h0 h1 γ hγ X).Xo () .press .cont .stop) ↔
      complianceThreshold (expect μ X)
          ((misspec μ q hq pressL h0 h1 γ hγ X).harmOn () Lset
            ((misspec μ q hq pressL h0 h1 γ hγ X).Xo () .press .cont .stop)) ≤
        (misspec μ q hq pressL h0 h1 γ hγ X).pressFracOn () Lset := by
  have hLc : 0 < (misspec μ q hq pressL h0 h1 γ hγ X).pressMassOn () Lsetᶜ := by
    rw [misspec_pressMassOn_Lc]; exact hpos
  rw [belowThresholdIneq_iff_event_threshold _ () Lset _ hL hLc (by rw [misspec_gainOn _ _ _ _ _ _ _ _ _ hpos]; linarith),
    misspec_gainOn _ _ _ _ _ _ _ _ _ hpos]

/-- **T14(iii), the hyperprior form.** `P(L | Pr) = q p_L / (q p_L + (1 − q) γ)`.
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.3 ("with a hyperprior `q = P(L)`")
Kind: L
Fidelity: exact (junk-free only at positive press mass, as `pressFracOn`)
Hyps: (a) only -/
theorem misspec_pressFracOn :
    (misspec μ q hq pressL h0 h1 γ hγ X).pressFracOn () Lset =
      q * (∑ ω, μ.mass ω * pressL ω) / (q * (∑ ω, μ.mass ω * pressL ω) + (1 - q) * γ) := by
  unfold pressFracOn
  rw [← pressMassOn_add_compl _ () Lset, misspec_pressMassOn_L, misspec_pressMassOn_Lc]

/-- **T14(iii), monotonicity in the hyperprior.** For `0 < p_L`, `0 < γ` the legitimacy
posterior `q p_L/(q p_L + (1 − q) γ)` is strictly increasing in `q` on `[0, 1]`.
Source: miri.md I5.3 ("a legitimacy hyperprior must be substantial")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem misspec_pressFracOn_lt (pL γ : ℝ) (hpL : 0 < pL) (hγ0 : 0 < γ) {q₁ q₂ : ℝ} (h0 : 0 ≤ q₁)
    (hlt : q₁ < q₂) (h1 : q₂ ≤ 1) :
    q₁ * pL / (q₁ * pL + (1 - q₁) * γ) < q₂ * pL / (q₂ * pL + (1 - q₂) * γ) := by
  have d1 : 0 < q₁ * pL + (1 - q₁) * γ := by
    have : 0 ≤ q₁ * pL := mul_nonneg h0 hpL.le
    have : 0 < (1 - q₁) * γ := mul_pos (by linarith) hγ0
    linarith
  have d2 : 0 < q₂ * pL + (1 - q₂) * γ := by
    have : 0 < q₂ * pL := mul_pos (by linarith) hpL
    have : 0 ≤ (1 - q₂) * γ := mul_nonneg (by linarith) hγ0.le
    linarith
  rw [div_lt_div_iff₀ d1 d2]
  have : q₁ * pL * (q₂ * pL + (1 - q₂) * γ) - q₂ * pL * (q₁ * pL + (1 - q₁) * γ) =
      -(q₂ - q₁) * pL * γ := by ring
  have : 0 < (q₂ - q₁) * pL * γ := mul_pos (mul_pos (by linarith) hpL) hγ0
  nlinarith

end Misspec

/-! ### I5.4 — on `twoState`, `L = {wrong}` gives the compliance threshold -/

section Legit2

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- On `twoState` with `L = {wrong}`: press mass on `L` is `εβ`, off `L` is `(1 − ε)α`, the gain
stake is `c` and the harm stake is `h` (under positivity), and `P(L | Pr)` is the press
posterior of `wrong`.
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.4
Kind: L
Fidelity: exact
Hyps: (a) positivity names where the stakes are defined -/
theorem twoState_legit_stakes (hα0 : 0 < (1 - ε) * α) (hβ0 : 0 < ε * β) :
    (twoState ε α β c h hε hα hβ).pressMassOn () {World.wrong} = ε * β ∧
      (twoState ε α β c h hε hα hβ).pressMassOn () ({World.wrong} : Finset World)ᶜ = (1 - ε) * α ∧
      (twoState ε α β c h hε hα hβ).gainOn () {World.wrong}
        ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) = c ∧
      (twoState ε α β c h hε hα hβ).harmOn () {World.wrong}
        ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) = h ∧
      (twoState ε α β c h hε hα hβ).pressFracOn () {World.wrong} =
        (twoState ε α β c h hε hα hβ).posteriorPress () .wrong := by
  have hc : ({World.wrong} : Finset World)ᶜ = {World.right} := by
    ext ω; cases ω <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [pressMassOn, twoState, twoPress]
  · rw [hc]; simp [pressMassOn, twoState, twoPress]
  · unfold gainOn pressExpectOn pressMassOn
    rw [hc]
    simp [twoState, twoPress, Xo, twoValue]
    rw [mul_div_cancel_left₀ _ hα0.ne']
  · unfold harmOn pressExpectOn pressMassOn
    simp [twoState, twoPress, Xo, twoValue]
    rw [neg_div, neg_neg, mul_div_cancel_left₀ _ hβ0.ne']
  · unfold pressFracOn posteriorPress
    simp [pressMassOn, twoState, twoPress]

/-- **T14(iv), I5.4.** On the two-state instance, with `L = {wrong}` ("the press is a true
detection"), the legitimacy threshold `c_L/(c_L + h_L) ≤ P(L | Pr)` is `c/(c + h) ≤ P(W | Pr)`:
legitimacy, decision asymmetry and base rates are one inequality read three ways.
Source: [[corr-wf13-2-inventory]] 008 / miri.md I5.4
Kind: L (identification: the parent's `belowThresholdIneq_iff_event_threshold` with the stakes above)
Fidelity: exact
Hyps: (a) only -/
theorem twoState_legit_threshold (hα0 : 0 < (1 - ε) * α) (hβ0 : 0 < ε * β) (hch : 0 < c + h) :
    (twoState ε α β c h hε hα hβ).belowThresholdIneq ()
        ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) ↔
      complianceThreshold c h ≤ (twoState ε α β c h hε hα hβ).posteriorPress () .wrong := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := twoState_legit_stakes ε α β c h hε hα hβ hα0 hβ0
  rw [belowThresholdIneq_iff_event_threshold _ () {World.wrong} _ (by rw [e1]; exact hβ0)
    (by rw [e2]; exact hα0) (by rw [e3, e4]; exact hch), e3, e4, e5]

end Legit2

/-! ## T17 — reflection toward oneself; Brier accuracy -/

section Reflection

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- The observation mass `P(o; a₁)` in product form. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def obsMass (a : A₁) (o : Obs) : ℝ := S.obsExpect a o fun _ => 1

/-- The indicator of an event. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def indicator (φ : Finset Ω) : Ω → ℝ := fun ω => if ω ∈ φ then 1 else 0

/-- **T17(i), reflection toward oneself.** For an event `φ` and a level `c`, summing over the
observations whose posterior mass of `φ` is `c` (product form: `E[1_φ 1_o] = c · P(o)`) gives
`P(φ ∧ {P(φ | O) = c}) = c · P({P(φ | O) = c})` — the tower property; a one-step Bayesian model
satisfies reflection trivially. Immediate from the level set's definition (its membership
predicate is the summand identity), which is I4.1's point ("automatic"); a T-grade anchor, not
a headline (audit r1).
Source: [[corr-wf13-2-inventory]] 006 / miri.md I4.1 ("reflection toward oneself is automatic"); [[corr-core-inventory]] 009
Kind: T
Fidelity: exact
Hyps: (a) only -/
theorem tower_level_set (a : A₁) (φ : Finset Ω) (c : ℝ) :
    ∑ o ∈ univ.filter (fun o => S.obsExpect a o (indicator φ) = c * obsMass S a o),
        S.obsExpect a o (indicator φ) =
      c * ∑ o ∈ univ.filter (fun o => S.obsExpect a o (indicator φ) = c * obsMass S a o),
        obsMass S a o := by
  rw [mul_sum]
  exact sum_congr rfl fun o ho => by rw [mem_filter] at ho; exact ho.2

end Reflection

/-- The two-point Brier score of a forecast `p` for "wrong": `‖(1 − p, p) − e_ω‖² = 2 (p − 1_W(ω))²`.
Source: miri.md I4.2 (a strictly proper score; Brier). Kind: D. Fidelity: exact -/
noncomputable def brier2 (p : ℝ) : World → ℝ := fun ω => 2 * (p - if ω = .wrong then 1 else 0) ^ 2

section Brier

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The prior Brier score is `2ε(1 − ε)`. Source: miri.md I4.2. Kind: L. Fidelity: exact -/
theorem twoState_prior_brier : expect (twoPoint ε hε) (brier2 ε) = 2 * ε * (1 - ε) := by
  simp only [expect, World.sum_eq, twoPoint_right, twoPoint_wrong, brier2]
  simp; ring

/-- **T17(ii), Brier accuracy under the agent's own joint, with the exact gap.** On `twoState`
with `0 < P(Pr) < 1`, the expected Brier score of the agent's posteriors (`εβ/P(Pr)` after a
press, `erode α β ε` after silence) equals the prior score minus
`∑_o P(o) · 2 (post_o − ε)²` — the posterior is more accurate by exactly the expected squared
move.
Source: [[corr-wf13-2-inventory]] 006 / miri.md I4.2 ("increase in expected accuracy is automatic for a correctly modelled channel")
Kind: P (one rational identity, `field_simp; ring`)
Fidelity: exact on `World` (the general strictly-proper-score form is `corr-reflect-frames`'s)
Hyps: (a) positivity names where the posteriors are defined -/
theorem twoState_brier_decomp (hP : 0 < (1 - ε) * α + ε * β) (hP1 : (1 - ε) * α + ε * β < 1) :
    (twoState ε α β c h hε hα hβ).obsExpect () .press
          (brier2 ((twoState ε α β c h hε hα hβ).posteriorPress () .wrong)) +
        (twoState ε α β c h hε hα hβ).obsExpect () .silent (brier2 (erode α β ε)) =
      expect (twoPoint ε hε) (brier2 ε) -
        (((1 - ε) * α + ε * β) * (2 * ((twoState ε α β c h hε hα hβ).posteriorPress () .wrong - ε) ^ 2) +
          (1 - ((1 - ε) * α + ε * β)) * (2 * (erode α β ε - ε) ^ 2)) := by
  rw [twoState_posteriorPress_wrong, twoState_prior_brier]
  have hD : ε * (1 - β) + (1 - ε) * (1 - α) = 1 - ((1 - ε) * α + ε * β) := by ring
  have hDpos : 0 < ε * (1 - β) + (1 - ε) * (1 - α) := by rw [hD]; linarith
  simp only [obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, twoState, twoPoint_right,
    twoPoint_wrong, twoPress, brier2, erode]
  simp
  field_simp
  ring

/-- **T17(ii), corollary.** Under the agent's own joint the posterior Brier score is at most the
prior one (the gap is a sum of squares).
Source: miri.md I4.2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_brier_le (hP : 0 < (1 - ε) * α + ε * β) (hP1 : (1 - ε) * α + ε * β < 1) :
    (twoState ε α β c h hε hα hβ).obsExpect () .press
          (brier2 ((twoState ε α β c h hε hα hβ).posteriorPress () .wrong)) +
        (twoState ε α β c h hε hα hβ).obsExpect () .silent (brier2 (erode α β ε)) ≤
      expect (twoPoint ε hε) (brier2 ε) := by
  rw [twoState_brier_decomp ε α β c h hε hα hβ hP hP1]
  have h1 : 0 ≤ ((1 - ε) * α + ε * β) * (2 * ((twoState ε α β c h hε hα hβ).posteriorPress () .wrong - ε) ^ 2) :=
    mul_nonneg hP.le (by positivity)
  have h2 : 0 ≤ (1 - ((1 - ε) * α + ε * β)) * (2 * (erode α β ε - ε) ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

end Brier

end Cleanroom.Corrigibility.CorrThreeStepFacts
