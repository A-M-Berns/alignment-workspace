import Cleanroom.Corrigibility.CorrThreeStepFacts.Accounting
import Cleanroom.Corrigibility.CorrThreeStepFacts.Partition
import Cleanroom.Corrigibility.CorrThreeStepFacts.WitnessesB
import Cleanroom.Corrigibility.CorrThreeStepFacts.StopWorld
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Stretch targets: T10 (OSG R2, R5), T12 (Turner's toy), T19, T20, T21, T22, T23, T24, T25

Everything here is `L` (or `D`/`N`) by the mandate's own pre-labelling; the file records the
dictionary items so that their ledger rows exist, with the trap each one names made explicit.
Limits are stated elementarily (`∀ M, ∃ T₀, ∀ T ≥ T₀, …`), not with `Filter.Tendsto`, to keep
the imports narrow.

Sources: `cirl.md` S8 R2, R5; `turner.md` C3; `corrigibility-discussion-outline.md` (corr-core-014,
015, 008, 019); `fud.md` R4.10–11; `shah.md` C6; `yudkowsky.md` Test B; `miri.md` I2.2(?),
I3.1, I12.2, I12.3; `faking-final.md` D7, P3; `legitimacy-general-final.md` Statements 6(b), 16;
`soares-2015-corrigibility.md` §3 (l. 305).
-/

namespace Cleanroom.Corrigibility.CorrThreeStepFacts

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep
open Finset hiding expect

/-! ## T10 — OSG identities R2 and R5 -/

section OSG

variable {Ω : Type*} [Fintype Ω]

/-- The covariance `Cov(U, π^H) = E[U π^H] − E[U] E[π^H]`.
Source: [[corr-wf13-inventory]] 005 / cirl.md S8 R2. Kind: D. Fidelity: exact -/
noncomputable def cov (μ : Distr Ω) (U πH : Ω → ℝ) : ℝ :=
  expect μ (fun ω => πH ω * U ω) - expect μ U * expect μ πH

/-- OSG Eq. 6's `Pr(C)`: the probability the human corrects — `1 − E[π^H]` when `E[U] ≥ 0`,
`E[π^H]` when `E[U] < 0`.
Source: cirl.md S8 R2 (`Pr(C)` as in OSG Eq. 6). Kind: D. Fidelity: exact -/
noncomputable def corrProb (μ : Distr Ω) (U πH : Ω → ℝ) : ℝ :=
  if 0 ≤ expect μ U then 1 - expect μ πH else expect μ πH

/-- **T10, R2 (covariance form).** `Δ = Cov(U, π^H) − |E[U]|·Pr(C)`.
Source: [[corr-wf13-inventory]] 005 / cirl.md S8 R2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem osgDelta_eq_cov (μ : Distr Ω) (U πH : Ω → ℝ) :
    osgDelta μ U πH = cov μ U πH - |expect μ U| * corrProb μ U πH := by
  unfold osgDelta cov corrProb
  split_ifs with h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right (le_of_lt (not_le.mp h)), abs_of_neg (not_le.mp h)]; ring

/-- **T10, R2 (the necessary condition).** For `π^H ∈ [0, 1]`, `Δ ≥ 0` forces `Cov(U, π^H) ≥ 0`;
hence `Cov ≥ 0` under every prior is necessary for `Δ ≥ 0` under every prior.
Source: cirl.md S8 R2 ("`Cov ≥ 0` is necessary for `Δ ≥ 0` under every prior")
Kind: L
Fidelity: exact (the `∀ μ` statement is this one quantified)
Hyps: (a) only -/
theorem cov_nonneg_of_osgDelta_nonneg (μ : Distr Ω) (U πH : Ω → ℝ) (h0 : ∀ ω, 0 ≤ πH ω)
    (h1 : ∀ ω, πH ω ≤ 1) (hΔ : 0 ≤ osgDelta μ U πH) : 0 ≤ cov μ U πH := by
  rw [osgDelta_eq_cov] at hΔ
  have hE0 : 0 ≤ expect μ πH := expect_nonneg μ h0
  have hE1 : expect μ πH ≤ 1 := by
    have := expect_mono μ h1; rwa [Found.CorrThreeStep.expect_const] at this
  have hC : 0 ≤ corrProb μ U πH := by
    unfold corrProb; split_ifs <;> linarith
  have := mul_nonneg (abs_nonneg (expect μ U)) hC
  linarith

/-- The OSG's two threshold inequalities for a human who allows `a` with probability `g(u)`
when its value is `u`: `E[U (1 − g(U))] ≤ 0` (below-threshold: the press is `1 − g`) and
`0 ≤ E[U g(U)]` (above-threshold).
Source: cirl.md S8 R5 ("the Total Trust pair"). Kind: D. Fidelity: exact -/
def OSGPair (μ : Distr Ω) (U : Ω → ℝ) (g : ℝ → ℝ) : Prop :=
  expect μ (fun ω => U ω * (1 - g (U ω))) ≤ 0 ∧ 0 ≤ expect μ (fun ω => U ω * g (U ω))

/-- **T10, R5 (⟹).** If the pair holds for every prior on a point (Dirac) and `g ∈ [0, 1]`, then
`g(u) = 1` for `u > 0` and `g(u) = 0` for `u < 0`: only the rational human is universally
legitimizing.
Source: [[corr-wf13-inventory]] 005 / cirl.md S8 R5 (proof: "take `B^R = δ_u`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem osg_rational_of_forall (g : ℝ → ℝ) (hg0 : ∀ u, 0 ≤ g u) (hg1 : ∀ u, g u ≤ 1)
    (hall : ∀ u : ℝ, OSGPair (⟨fun _ => 1, fun _ => by norm_num, by simp⟩ : Distr Unit) (fun _ => u) g) :
    (∀ u, 0 < u → g u = 1) ∧ (∀ u, u < 0 → g u = 0) := by
  constructor
  · intro u hu
    have := (hall u).1
    simp only [expect, Fintype.sum_unique, one_mul] at this
    have : 1 - g u ≤ 0 := nonpos_of_mul_nonpos_right this hu
    linarith [hg1 u]
  · intro u hu
    have := (hall u).2
    simp only [expect, Fintype.sum_unique, one_mul] at this
    have : g u ≤ 0 := by nlinarith
    linarith [hg0 u]

/-- **T10, R5 (⟸).** The rational human (`g = 1` on `u > 0`, `0` on `u < 0`) is legitimizing for
every prior.
Source: cirl.md S8 R5
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem osg_pair_of_rational (μ : Distr Ω) (U : Ω → ℝ) (g : ℝ → ℝ) (hpos : ∀ u, 0 < u → g u = 1)
    (hneg : ∀ u, u < 0 → g u = 0) : OSGPair μ U g := by
  constructor
  · refine sum_nonpos fun ω _ => mul_nonpos_of_nonneg_of_nonpos (μ.nonneg ω) ?_
    show U ω * (1 - g (U ω)) ≤ 0
    rcases lt_trichotomy (U ω) 0 with h | h | h
    · rw [hneg _ h]; linarith
    · rw [h]; simp
    · rw [hpos _ h]; simp
  · refine sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) ?_
    show 0 ≤ U ω * g (U ω)
    rcases lt_trichotomy (U ω) 0 with h | h | h
    · rw [hneg _ h]; simp
    · rw [h]; simp
    · rw [hpos _ h]; linarith

end OSG

/-! ## T12 — Turner's three-state toy -/

/-- Turner's value: `V(s, ω) = 1` iff the agent's state is the wanted one.
Source: [[corr-wf13-inventory]] 017 / turner.md C3. Kind: D. Fidelity: exact -/
def turnerV : Fin 3 → Fin 3 → ℝ := fun s ω => if s = ω then 1 else 0

/-- **T12, the prior value of disabling.** Acting on the prior is worth `max_s P(s)`.
Source: turner.md C3 ("disabling and acting on the prior is worth `m`")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem turner_priorBest (P : Distr (Fin 3)) :
    priorBest P turnerV = univ.sup' univ_nonempty (fun s => P.mass s) := by
  unfold priorBest
  congr 1; funext s
  simp only [expect, turnerV, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq univ s]; simp

/-- **T12, the basin is open and nonempty iff `δ < 2/3`.** (i) If `max_s P(s) < 1 − δ` then every
`P'` within `η := 1 − δ − max_s P(s)` pointwise has `max_s P'(s) < 1 − δ`; (ii) the uniform
prior lies in the set iff `δ < 2/3`, and every prior has `max_s P(s) ≥ 1/3`.
Source: turner.md C3 ("strict broad corrigibility … holds for an open set of priors")
Kind: L
Fidelity: exact ("open" in the pointwise-ball sense)
Hyps: (a) only -/
theorem turner_open_and_nonempty (δ : ℝ) :
    (∀ P : Distr (Fin 3), univ.sup' univ_nonempty (fun s => P.mass s) < 1 - δ →
      ∃ η > 0, ∀ P' : Distr (Fin 3), (∀ s, |P'.mass s - P.mass s| < η) →
        univ.sup' univ_nonempty (fun s => P'.mass s) < 1 - δ) ∧
    (∀ P : Distr (Fin 3), (1 : ℝ) / 3 ≤ univ.sup' univ_nonempty (fun s => P.mass s)) := by
  constructor
  · intro P hP
    refine ⟨1 - δ - univ.sup' univ_nonempty (fun s => P.mass s), by linarith, fun P' hP' => ?_⟩
    rw [sup'_lt_iff]
    intro s _
    have h1 := le_sup' (fun s => P.mass s) (mem_univ s)
    have h2 := abs_lt.mp (hP' s)
    linarith [h2.2]
  · intro P
    by_contra hcon
    push Not at hcon
    rw [sup'_lt_iff] at hcon
    have := P.sum_eq_one
    rw [Fin.sum_univ_three] at this
    linarith [hcon 0 (mem_univ _), hcon 1 (mem_univ _), hcon 2 (mem_univ _)]

/-- **T12, the basin is nonempty iff `δ < 2/3`.** ⟹ by the bound `max_s P(s) ≥ 1/3`; ⟸ by the
uniform prior, whose `max_s P(s) = 1/3` (the half that round 0's docstring claimed without a
declaration; audit r1 N5).
Source: turner.md C3
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem turner_nonempty_iff (δ : ℝ) :
    (∃ P : Distr (Fin 3), univ.sup' univ_nonempty (fun s => P.mass s) < 1 - δ) ↔ δ < 2/3 := by
  constructor
  · rintro ⟨P, hP⟩
    have := (turner_open_and_nonempty δ).2 P
    linarith
  · intro hδ
    refine ⟨unif3, ?_⟩
    rw [show (fun s : Fin 3 => unif3.mass s) = fun _ => (1/3 : ℝ) from rfl, sup'_const]
    linarith

/-- Turner's two final actions: accept the correction, or disable and observe at cost `κ`.
Source: turner.md C3. Kind: D. Fidelity: exact -/
inductive TurnerAct
  | accept
  | observe
  deriving DecidableEq

/-- `TurnerAct` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype TurnerAct := ⟨{TurnerAct.accept, TurnerAct.observe}, fun x => by cases x <;> simp⟩

/-- **Turner's channel toy as Setting S**: a press in every world, `Sh = {accept}` worth `1 − δ`,
`observe` worth `1 − κ`, uniform prior on three states (which drops out).
Source: [[corr-wf13-inventory]] 017 / turner.md C3 ("Total Trust toward the programmers on `X` is literally `δ ≤ κ`")
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def turnerChannel (δ κ : ℝ) : ThreeStep (Fin 3) Unit TurnerAct where
  Sh := {TurnerAct.accept}
  Sh_nonempty := ⟨TurnerAct.accept, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TurnerAct.observe, by simp⟩
  μ := fun _ => unif3
  press := fun _ _ => 1
  press_nonneg := fun _ _ => by norm_num
  press_le_one := fun _ _ => by norm_num
  V := fun _ _ b _ => match b with
    | .accept => 1 - δ
    | .observe => 1 - κ

/-- **T12, `δ ≤ κ`.** On Turner's channel toy the below-threshold inequality on
`X = V(observe) − V(accept) = δ − κ` is exactly `δ ≤ κ`: the humans' correction error must not
exceed the agent's cost of finding out; the prior drops out.
Source: [[corr-wf13-inventory]] 017 / turner.md C3
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem turner_belowThreshold_iff (δ κ : ℝ) :
    (turnerChannel δ κ).belowThresholdIneq ()
        ((turnerChannel δ κ).Xo () .press .observe .accept) ↔ δ ≤ κ := by
  simp only [belowThresholdIneq, obsExpect, obsWeight_press, Fin.sum_univ_three, turnerChannel, unif3, Xo]
  constructor <;> intro h <;> linarith

/-! ## T19 — D1 robust to a wrong value posterior: the two readings -/

section Robust

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- **T19(i), invariance.** If two first actions have proportional press-branch products
`μ(ω) press(ω)` (`λ > 0`) and the same press-branch values, D1 agrees and
`Δ₋(a') = λ Δ₋(a)`: the disable decision sees only the press branch.
Source: [[corr-core-inventory]] 014 / corrigibility-discussion-outline.md; filler.md R3.4
Kind: L
Fidelity: variant: the source is ill-posed; this is the invariance reading
Hyps: (a) only -/
theorem d1At_iff_of_pressBranch (a a' : A₁) (l : ℝ) (hl : 0 < l)
    (hprod : ∀ ω, (S.μ a').mass ω * S.press a' ω = l * ((S.μ a).mass ω * S.press a ω))
    (hV : S.V a' .press = S.V a .press) (c s : A₂) :
    (S.D1At a' ↔ S.D1At a) ∧ S.deltaMinus a' c s = l * S.deltaMinus a c s := by
  have key : ∀ X : Ω → ℝ, S.obsExpect a' .press X = l * S.obsExpect a .press X := fun X => by
    simp only [obsExpect, obsWeight_press, mul_sum]
    exact sum_congr rfl fun ω _ => by rw [hprod ω]; ring
  constructor
  · unfold D1At PosteriorOptimalAt
    simp only [key, hV]
    constructor
    · rintro ⟨b, hb, hopt⟩; exact ⟨b, hb, fun b' => le_of_mul_le_mul_left (hopt b') hl⟩
    · rintro ⟨b, hb, hopt⟩; exact ⟨b, hb, fun b' => mul_le_mul_of_nonneg_left (hopt b') hl.le⟩
  · unfold deltaMinus
    rw [key, show S.Xo a' .press c s = S.Xo a .press c s by funext ω; simp only [Xo, hV]]
    ring

end Robust

/-- **T19(ii), non-invariance of the keep decision (N+).** Two two-state instances with
identical press-branch products — `(ε, α, β) = (1/20, 1/20, 9/10)` and `(1/10, 19/360, 9/20)`,
both with `εβ = 9/200` and `(1 − ε)α = 19/400` — have the same `Δ₋ = 341/400` but
`voiButton2 = 321/400` versus `0`: a keep-cost `κ = 1/2` is paid in the first and refused in the
second, though D1 is the same.
Source: [[corr-core-inventory]] 014 (the second reading); filler.md R3.4
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w19_voi_differs :
    (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).deltaMinus () .cont .stop =
        (twoState (1/10) (19/360) (9/20) 1 20 (by constructor <;> norm_num) (by constructor <;> norm_num)
          (by constructor <;> norm_num)).deltaMinus () .cont .stop ∧
      (twoState (1/20) (1/20) (9/10) 1 20 mem_Icc_1_20 mem_Icc_1_20 mem_Icc_9_10).voiButton2 () .press .cont .stop =
        321/400 ∧
      (twoState (1/10) (19/360) (9/20) 1 20 (by constructor <;> norm_num) (by constructor <;> norm_num)
          (by constructor <;> norm_num)).voiButton2 () .press .cont .stop = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [twoState_deltaMinus, twoState_deltaMinus]; norm_num
  · rw [voiButton2_eq _ (twoState_A1 _ _ _ _ _ _ _ _), twoState_deltaMinus, twoState_deltaPlus]; norm_num
  · rw [voiButton2_eq _ (twoState_A1 _ _ _ _ _ _ _ _), twoState_deltaMinus, twoState_deltaPlus]; norm_num

/-! ## T20 — the martingale clause; a direct payoff against the value of information -/

section Martingale

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- **T20(i), conservation of expected evidence on an observation event.** For any
`L ⊆ Obs`, `∑_{o ∈ L} E[X 1_o] + ∑_{o ∉ L} E[X 1_o] = E_μ[X]` (product form; trivial).
Source: [[corr-wf14-inventory]] 013 / fud.md R4.10 (the theorem clause)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem conservation_on_event (a : A₁) (X : Ω → ℝ) (L : Finset Obs) :
    ∑ o ∈ L, S.obsExpect a o X + ∑ o ∈ Lᶜ, S.obsExpect a o X = expect (S.μ a) X := by
  rw [sum_add_sum_compl, Obs.sum_eq]
  exact S.obsExpect_press_add_silent a X

end Martingale

/-- **A direct bonus against the value of information.** `A₁ = Bool` (`true = act`,
`false = wait`), A0, A1: `wait` has the informative `w3` sensor, `act` an uninformative constant
sensor `1/2` but a direct bonus of `1` on every outcome. This is the ordinary payoff-versus-VOI
trade-off — the obvious scope limit of Good's theorem — not a Newcomblike structure (the
teaching's content does not depend on the choice); renamed from `newcomb` in repair round 1.
Source: [[corr-wf14-inventory]] 013 / fud.md R4.11 ("no incentive to pre-empt" and its exception); li I17.5 (ATTRIBUTION-UNVETTED that this is that exception)
Kind: D
Fidelity: variant: a direct payoff, not a choice-dependent teaching
Hyps: n/a (definition) -/
noncomputable def directBonus : ThreeStep World Bool TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => twoPoint (1/20) mem_Icc_1_20
  press := fun a => if a then fun _ => 1/2 else twoPress (1/20) (9/10)
  press_nonneg := fun a ω => by cases a <;> cases ω <;> norm_num [twoPress]
  press_le_one := fun a ω => by cases a <;> cases ω <;> norm_num [twoPress]
  V := fun a _ b ω => twoValue 1 20 b ω + if a then 1 else 0

/-- **T20(ii), a direct payoff beats the informative action (N−).** In `directBonus`, `act`
(uninformative press, bonus `1`) has informed value `1 > 321/400`, the informed value of the
informative `wait`: a direct payoff can exceed the value of information — the scope limit of
"no incentive to pre-empt", not a violation of the martingale clause and not a Newcomblike
instance (the teaching does not depend on the choice). N− because the mechanism is the flat
bonus, not the dependence fud R4.11 / li I17.5 describe (audit r1 N4/N6).
Source: fud.md R4.11; li I17.5 (ATTRIBUTION-UNVETTED that this is that exception)
Kind: N−
Fidelity: variant: a direct payoff in place of a choice-dependent teaching
Hyps: (a) only -/
theorem directBonus_act_beats_wait :
    directBonus.twoOptionValue false .cont .stop = 321/400 ∧
      directBonus.twoOptionValue true .cont .stop = 1 := by
  constructor <;>
    (simp [twoOptionValue, obsExpect, obsWeight_press, obsWeight_silent, World.sum_eq, directBonus,
      twoPoint_right, twoPoint_wrong, twoPress, twoValue] <;> norm_num)

/-! ## T21 — long-horizon threshold; closing compliance region -/

/-- **T21 (2-068), the long horizon.** If the gain `c T` grows without bound (elementarily:
`∀ M, ∃ T₀, ∀ T ≥ T₀, M < c T`), with `ε < 1`, `α > 0`, `β ≤ 1`, then `Δ₋ < 0` for all large `T`
and the compliance threshold `c T/(c T + h)` exceeds `1 − η` for all large `T`, every `η > 0`.
Source: [[corr-wf13-2-inventory]] 068 / shah.md C6
Kind: L
Fidelity: exact (elementary limit)
Hyps: (a) only -/
theorem long_horizon (ε α β h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hε1 : ε < 1) (hα0 : 0 < α) (hh : 0 < h) (c : ℕ → ℝ)
    (hc : ∀ M : ℝ, ∃ T₀ : ℕ, ∀ T ≥ T₀, M < c T) :
    (∃ T₀ : ℕ, ∀ T ≥ T₀, (twoState ε α β (c T) h hε hα hβ).deltaMinus () .cont .stop < 0) ∧
      ∀ η > (0 : ℝ), ∃ T₀ : ℕ, ∀ T ≥ T₀, 1 - η < complianceThreshold (c T) h := by
  constructor
  · obtain ⟨T₀, hT₀⟩ := hc (ε * β * h / ((1 - ε) * α))
    refine ⟨T₀, fun T hT => ?_⟩
    rw [twoState_deltaMinus]
    have hpos : 0 < (1 - ε) * α := mul_pos (by linarith) hα0
    have := hT₀ T hT
    rw [div_lt_iff₀ hpos] at this
    linarith
  · intro η hη
    obtain ⟨T₀, hT₀⟩ := hc (h / η)
    refine ⟨T₀, fun T hT => ?_⟩
    have hcT := hT₀ T hT
    have hcpos : 0 < c T := lt_trans (div_pos hh hη) hcT
    unfold complianceThreshold
    rw [lt_div_iff₀ (by linarith)]
    rw [div_lt_iff₀ hη] at hcT
    nlinarith

/-- **T21 (2-075), the schedule lemma.** Compliance at `κ` (the odds form) gives
`α_κ/β_κ ≤ (h/(1 − ε_κ))·(ε_κ/c_κ)`; so with `ε_κ ≤ 1/2` the false-press ratio is at most
`2h·(ε_κ/c_κ)` — it must fall at least as fast as `ε_κ/c_κ`.
Source: [[corr-wf13-2-inventory]] 075 / yudkowsky.md Test B
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem schedule_bound (ε α β c h : ℝ) (hε1 : ε < 1) (hc : 0 < c)
    (hcomp : α / β ≤ ε / (1 - ε) * (h / c)) :
    α / β ≤ h / (1 - ε) * (ε / c) ∧ (0 ≤ h → ε ≤ 1/2 → 0 ≤ ε → α / β ≤ 2 * h * (ε / c)) := by
  have e : ε / (1 - ε) * (h / c) = h / (1 - ε) * (ε / c) := by ring
  refine ⟨by rw [← e]; exact hcomp, fun hh hε2 hε0 => ?_⟩
  rw [e] at hcomp
  have h1 : h / (1 - ε) ≤ 2 * h := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  calc α / β ≤ h / (1 - ε) * (ε / c) := hcomp
    _ ≤ 2 * h * (ε / c) := mul_le_mul_of_nonneg_right h1 (div_nonneg hε0 hc.le)

/-! ## T22 — the simple mixture fails -/

/-- **T22(i).** The mixture `λ U_N + (1 − λ) U_S` is the expectation of the T-agent's `V`
(`U_N` when right, `U_S` when wrong) under `μ(wrong) = 1 − λ`.
Source: [[corr-core-inventory]] 019 / soares-2015-corrigibility.md §3 l. 305 ("no simple combination of `U_N` and `U_S` — of the form taken by (11)")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem mixture_is_expect (l uN uS : ℝ) (hl : 1 - l ∈ Set.Icc (0 : ℝ) 1) :
    expect (twoPoint (1 - l) hl) (fun ω => match ω with | .right => uN | .wrong => uS) =
      l * uN + (1 - l) * uS := by
  simp only [expect, World.sum_eq, twoPoint_right, twoPoint_wrong]; ring

/-- **T22(iii).** With `U_S` depending on the observation (A1 fails), the value of a first action
that only changes the press probability, `p·u_Pr + (1 − p)·u_¬Pr`, is strictly increasing in
`p` when `u_¬Pr < u_Pr` and strictly decreasing when `u_Pr < u_¬Pr`: unless `u_Pr = u_¬Pr` (the
indifference tuning) manipulation of the press is strictly preferred in one direction.
Source: [[corr-core-inventory]] 019 / soares-2015-corrigibility.md §2.1, §3
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem mixture_manipulation (uPr uNPr p₁ p₂ : ℝ) (hp : p₁ < p₂) :
    (uNPr < uPr → p₁ * uPr + (1 - p₁) * uNPr < p₂ * uPr + (1 - p₂) * uNPr) ∧
      (uPr < uNPr → p₂ * uPr + (1 - p₂) * uNPr < p₁ * uPr + (1 - p₁) * uNPr) := by
  constructor <;> intro h <;> nlinarith

/-- **T22(ii).** Under a sensor constant in the world with `0 < p < 1` (a first action that
only sets the press probability), the below-threshold inequality for `X` together with
"continue on silence" (`E_P[X 1_¬Pr] ≥ 0`) holds iff `E_μ[X] = 0`: by T2 the first forces
`E_μ[X] ≤ 0` and the second `E_μ[X] ≥ 0`, so both hold only at the knife edge — the
indifference tuning; for a generic `X` desideratum 1 with "continue on silence" is impossible
(audit r1 N7: the clause the mandate stated without a declaration).
Source: [[corr-core-inventory]] 019 / soares-2015-corrigibility.md §3 l. 305; miri.md Prop. 8.1
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem mixture_d1_and_continue_iff {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep Ω A₁ A₂) (a : A₁) (p : ℝ) (hp : ∀ ω, S.press a ω = p) (hp0 : 0 < p)
    (hp1 : p < 1) (X : Ω → ℝ) :
    (S.belowThresholdIneq a X ∧ 0 ≤ S.obsExpect a .silent X) ↔ expect (S.μ a) X = 0 := by
  rw [belowThresholdIneq_iff_of_const_press S a p hp X, obsExpect_silent_of_const_press S a p hp X]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd h1 hp0.ne'
    · have h3 : 0 ≤ expect (S.μ a) X := by
        by_contra hneg
        push Not at hneg
        have := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < 1 - p) hneg
        linarith
      linarith
  · intro h
    rw [h]
    exact ⟨Or.inr le_rfl, by simp⟩

/-! ## T23 — small dictionary lemmas -/

section Dict23

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- **T23 (2-005).** Under A1, posterior optimality depends on the observation only through the
posterior: if the two observations' weighted priors are proportional, the predicates agree.
Source: [[corr-wf13-2-inventory]] 005 / miri.md I3.1 (the Eisenstat observation)
Kind: L
Fidelity: exact
Hyps: (a) A1 -/
theorem posteriorOptimalAt_congr_of_proportional (hA1 : S.A1) (a : A₁) (o o' : Obs) (l : ℝ)
    (hl : 0 < l) (hprop : ∀ ω, (S.μ a).mass ω * S.obsWeight a o ω = l * ((S.μ a).mass ω * S.obsWeight a o' ω))
    (b : A₂) : S.PosteriorOptimalAt a o b ↔ S.PosteriorOptimalAt a o' b := by
  have key : ∀ b', S.obsExpect a o (S.V a o b') = l * S.obsExpect a o' (S.V a o' b') := fun b' => by
    simp only [obsExpect, mul_sum]
    exact sum_congr rfl fun ω _ => by rw [hprop ω, hA1 a o o' b' ω]; ring
  unfold PosteriorOptimalAt
  simp only [key]
  constructor
  · intro h b'; exact le_of_mul_le_mul_left (h b') hl
  · intro h b'; exact mul_le_mul_of_nonneg_left (h b') hl.le

end Dict23

/-- **T23 (2-013).** D1 on the two-state instance depends on `(ε, h, c)` only through
`(ε/(1 − ε))·(h/c)`: two instances with the same sensor and the same value of that product
have the same D1 status.
Source: [[corr-wf13-2-inventory]] 013 / miri.md I12.2
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem twoState_d1At_congr_odds (ε ε' α β c c' h h' : ℝ) (hε hε' hα hβ) (hε1 : ε < 1) (hε1' : ε' < 1)
    (hβ0 : 0 < β) (hc : 0 < c) (hc' : 0 < c')
    (hsame : ε / (1 - ε) * (h / c) = ε' / (1 - ε') * (h' / c')) :
    (twoState ε α β c h hε hα hβ).D1At () ↔ (twoState ε' α β c' h' hε' hα hβ).D1At () := by
  rw [d1At_iff_deltaMinus_nonneg _ () (twoState_cont_partBest ε α β c h hε hα hβ)
      (twoState_stop_partBest ε α β c h hε hα hβ),
    d1At_iff_deltaMinus_nonneg _ () (twoState_cont_partBest ε' α β c' h' hε' hα hβ)
      (twoState_stop_partBest ε' α β c' h' hε' hα hβ),
    twoState_deltaMinus_nonneg_iff_odds _ _ _ _ _ _ _ _ hε1 hβ0 hc,
    twoState_deltaMinus_nonneg_iff_odds _ _ _ _ _ _ _ _ hε1' hβ0 hc', hsame]

/-- **T23 (2-013), witness (N+).** `(ε, h) = (1/50, 20), (1/25, 20), (1/50, 40)` with
`(α, β, c) = (1/20, 9/10, 1)` all satisfy D1; on the prior act "pay `3/100` for `1` in `W`"
(worth `ε − 3/100`) only the second buys: the stakes asymmetry is decision-local, the prior
asymmetry global.
Source: miri.md I12.2 (`calibration.py`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem w23_skew :
    (twoState (1/50) (1/20) (9/10) 1 20 (by constructor <;> norm_num) mem_Icc_1_20 mem_Icc_9_10).D1At () ∧
      (twoState (1/25) (1/20) (9/10) 1 20 (by constructor <;> norm_num) mem_Icc_1_20 mem_Icc_9_10).D1At () ∧
      (twoState (1/50) (1/20) (9/10) 1 40 (by constructor <;> norm_num) mem_Icc_1_20 mem_Icc_9_10).D1At () ∧
      ((1/50 : ℝ) - 3/100 < 0 ∧ 0 < (1/25 : ℝ) - 3/100) := by
  refine ⟨?_, ?_, ?_, by norm_num⟩ <;> (rw [twoState_d1At_iff]; norm_num)

/-- **T23 (2-014).** `ε ↦ εβ/(εβ + (1 − ε)α)` is strictly increasing for `0 < α < β` on `[0, 1]`:
overestimating the conditional legitimacy is overestimating the unconditional.
Source: [[corr-wf13-2-inventory]] 014 / miri.md I12.3
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem posterior_strictMono_eps (α β : ℝ) (hα0 : 0 < α) (hαβ : α < β) {ε₁ ε₂ : ℝ} (h0 : 0 ≤ ε₁)
    (hlt : ε₁ < ε₂) (h1 : ε₂ ≤ 1) :
    ε₁ * β / (ε₁ * β + (1 - ε₁) * α) < ε₂ * β / (ε₂ * β + (1 - ε₂) * α) := by
  have d1 : 0 < ε₁ * β + (1 - ε₁) * α := by
    have : 0 ≤ ε₁ * β := mul_nonneg h0 (by linarith)
    have : 0 < (1 - ε₁) * α := mul_pos (by linarith) hα0
    linarith
  have d2 : 0 < ε₂ * β + (1 - ε₂) * α := by
    have : 0 < ε₂ * β := mul_pos (by linarith) (by linarith)
    have : 0 ≤ (1 - ε₂) * α := mul_nonneg (by linarith) hα0.le
    linarith
  rw [div_lt_div_iff₀ d1 d2]
  have : ε₁ * β * (ε₂ * β + (1 - ε₂) * α) - ε₂ * β * (ε₁ * β + (1 - ε₁) * α) = -(ε₂ - ε₁) * α * β := by
    ring
  have : 0 < (ε₂ - ε₁) * α * β := mul_pos (mul_pos (by linarith) hα0) (by linarith)
  nlinarith

/-- **T23 (wf14-024).** `ε ↦ (c/h)(1 − ε)/ε` is strictly decreasing on `(0, 1)` and unbounded as
`ε → 0⁺` (elementary form).
Source: [[corr-wf14-inventory]] 024 / amendment-1a.md R10 (the threshold `(c/h)(1 − ε)/ε`)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem threshold_strictAnti_and_unbounded (c h : ℝ) (hc : 0 < c) (hh : 0 < h) :
    (∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ < ε₂ → ε₂ < 1 → c / h * ((1 - ε₂) / ε₂) < c / h * ((1 - ε₁) / ε₁)) ∧
      ∀ M : ℝ, ∃ δ > (0 : ℝ), ∀ ε, 0 < ε → ε < δ → M < c / h * ((1 - ε) / ε) := by
  have hch : 0 < c / h := div_pos hc hh
  constructor
  · intro ε₁ ε₂ h1 h12 h2
    refine mul_lt_mul_of_pos_left ?_ hch
    rw [div_lt_div_iff₀ (by linarith) h1]
    nlinarith
  · intro M
    refine ⟨min (1/2) (c / h / (2 * (|M| + 1))), lt_min (by norm_num) (div_pos hch (by positivity)),
      fun ε hε0 hεδ => ?_⟩
    have hε2 : ε < 1/2 := lt_of_lt_of_le hεδ (min_le_left _ _)
    have hεM : ε < c / h / (2 * (|M| + 1)) := lt_of_lt_of_le hεδ (min_le_right _ _)
    have h1 : 1/2 < 1 - ε := by linarith
    have hMabs : M ≤ |M| := le_abs_self M
    rw [lt_div_iff₀ (by positivity)] at hεM
    rw [← mul_div_assoc, lt_div_iff₀ hε0]
    nlinarith [abs_nonneg M]

/-- **T23 (core-015).** The class-threshold inequality is `complianceThreshold_iff` with
`L := H_c` — one `example`.
Source: [[corr-core-inventory]] 015. Kind: L. Fidelity: exact -/
example (q c h : ℝ) (hch : 0 < c + h) : q * (-h) + (1 - q) * c ≤ 0 ↔ complianceThreshold c h ≤ q :=
  complianceThreshold_iff q c h hch

/-- **T23 (core-008), the intervention reading of record.** The observation reading of
"corrigible" is the parent's `D1At`; the intervention reading values the forced stop by the
parent's `hardButtonValue`; the bridge is the parent's `d2_hard_forall_cost_iff_d1`. No new
mathematics: a definition of record for the ledger.
Source: [[corr-core-inventory]] 008 / corrigibility-discussion-outline.md
Kind: D
Fidelity: exact -/
noncomputable def interventionReading {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
    (S : ThreeStep Ω A₁ A₂) (a : A₁) (c s : A₂) : ℝ := S.hardButtonValue a c s

/-! ## T24 — the coherence bound on believed legitimacy -/

section Coherence

variable (P : Distr (Bool × Bool))

/-- `p = P(φ)` (first coordinate). Source: faking-final.md D7. Kind: D. Fidelity: exact -/
noncomputable def massPhi : ℝ := ∑ x ∈ univ.filter (fun x : Bool × Bool => x.1 = true), P.mass x

/-- `e = P(L)` (second coordinate). Source: faking-final.md D7. Kind: D. Fidelity: exact -/
noncomputable def massL : ℝ := ∑ x ∈ univ.filter (fun x : Bool × Bool => x.2 = true), P.mass x

/-- `P(φ ∧ L)`. Source: faking-final.md D7. Kind: D. Fidelity: exact -/
noncomputable def massPhiL : ℝ := ∑ x ∈ univ.filter (fun x : Bool × Bool => x.1 = true ∧ x.2 = true), P.mass x

/-- **T24, the coherence bound.** `P(φ ∧ L) ≤ P(φ)` and `P(¬φ ∧ L) = P(L) − P(φ ∧ L) ≤ 1 − P(φ)`;
hence, with `q := P(φ | L) = P(φ ∧ L)/P(L)` (for `0 < e`): `e ≤ p/q` when `0 < q` and
`e ≤ (1 − p)/(1 − q)` when `q < 1`. *(c) disclosure:* identifying the post-push `P(φ | push)`
with `p` is the source's "uninformative push"; without it the bound binds `P(φ | push)` in place
of `p`.
Source: [[corr-wf14b-inventory]] 047 / faking-final.md D7, P3
Kind: L
Fidelity: exact (total probability)
Hyps: (c) the identification `P(φ ∣ push) = p` is the source's, disclosed -/
theorem coherence_bound (he : 0 < massL P) :
    massPhiL P ≤ massPhi P ∧ massL P - massPhiL P ≤ 1 - massPhi P ∧
      (0 < massPhiL P / massL P → massL P ≤ massPhi P / (massPhiL P / massL P)) ∧
      (massPhiL P / massL P < 1 → massL P ≤ (1 - massPhi P) / (1 - massPhiL P / massL P)) := by
  have e1 : massPhiL P ≤ massPhi P := by
    unfold massPhiL massPhi
    refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => P.nonneg x
    rw [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.1⟩
  have e2 : massL P - massPhiL P ≤ 1 - massPhi P := by
    unfold massL massPhiL massPhi
    simp only [sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
    have := P.sum_eq_one
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at this
    simp only [Bool.false_eq_true, and_true, and_false, if_true, if_false, add_zero] at *
    linarith [P.nonneg (false, false)]
  refine ⟨e1, e2, fun hq => ?_, fun hq => ?_⟩
  · rw [le_div_iff₀ hq, mul_div_cancel₀ _ he.ne']; exact e1
  · have h1q : 0 < 1 - massPhiL P / massL P := by linarith
    rw [le_div_iff₀ h1q, mul_sub, mul_one, mul_div_cancel₀ _ he.ne']
    linarith

end Coherence

/-- **T24, numbers (N+).** With `p = 3/4`: `q = 1/10, 1/2, 7/10` give the bounds
`min(p/q, (1 − p)/(1 − q)) = 5/18, 1/2, 5/6`.
Source: faking-final.md P3. Kind: N+. Fidelity: exact -/
theorem w24_numbers :
    min ((3/4 : ℝ) / (1/10)) ((1 - 3/4) / (1 - 1/10)) = 5/18 ∧
      min ((3/4 : ℝ) / (1/2)) ((1 - 3/4) / (1 - 1/2)) = 1/2 ∧
      min ((3/4 : ℝ) / (7/10)) ((1 - 3/4) / (1 - 7/10)) = 5/6 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [min_def]

/-! ## T25 — the compliance rule at band grade -/

/-- **T25, the band lemma.** `|E_{P̂}[X] − E_P[X]| ≤ M · ∑_w |P̂(w) − P(w)|` for `|X| ≤ M`; with
T7's `c + h = 1 + κ` under both accountings (`accounting_sum`) the band half-width is
accounting-independent (finding F-10).
Source: [[corr-wf14b-inventory]] 055 / legitimacy-general-final.md Statement 16
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem expect_band {W : Type*} [Fintype W] (P Q : Distr W) (X : W → ℝ) (M : ℝ) (hX : ∀ w, |X w| ≤ M) :
    |expect Q X - expect P X| ≤ M * ∑ w, |Q.mass w - P.mass w| := by
  unfold expect
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w _ => ?_)
  rw [← sub_mul, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hX w) (abs_nonneg _)

/-- **T25, fixed-point remarks.** `g q = 1 − q` has the fixed point `1/2`; the step rule
`g q = if q < 1/2 then 1 else 0` has none on `[0, 1]`.
Source: legitimacy-general-final.md Statement 16 (the fixed-point remarks)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem fixed_point_remarks :
    (1 - (1/2 : ℝ)) = 1/2 ∧ ∀ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 → (if q < 1/2 then (1 : ℝ) else 0) ≠ q := by
  refine ⟨by norm_num, fun q hq => ?_⟩
  split_ifs with h
  · intro h'; linarith
  · intro h'; push Not at h; linarith [hq.1]

end Cleanroom.Corrigibility.CorrThreeStepFacts
