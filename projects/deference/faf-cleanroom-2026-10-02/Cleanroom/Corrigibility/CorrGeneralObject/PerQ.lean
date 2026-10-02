import Cleanroom.Corrigibility.CorrGeneralObject.Conjunction
import Cleanroom.Corrigibility.CorrGeneralObject.ExampleA
import Cleanroom.Found.CorrThreeStep.TwoState

/-!
# corr-general-object — T4: the per-`Q` compliance rule under reflection-legitimacy

* **(a) L (load-bearing through its witnesses).** Under value-form legitimacy of `L` for
  `X_{Q,a}`, the harm stake is read off the target: `h_L(Q,a) = E_Q[V πQ − V a] ≥ 0` by
  `Q`-optimality of `πQ` (`harm_nonneg_of_isOptimal`, `harmOn_eq_of_valueLegit`,
  `harmOn_nonneg_of_valueLegit`). The identity is D11's value-form definition divided by the
  guard — a rewrite of the hypothesis, kind L (audit r1); the *content* of T4(a) is that the
  reading is D11's (not an accuracy reading: CE1, `ce1_witness`) and that the package is
  inhabited by a proper legitimacy event (`e2_legit_witness`, below).
* **(b) L.** The rule `E[X | E_Q] = −ℓ h_L + (1−ℓ) c_L` and the threshold `ℓ ≥ c_L/(c_L+h_L)`
  are `corr-three-step`'s `condExpPress_eq_event_split`, `belowThresholdIneq_iff_event_split`,
  `belowThresholdIneq_iff_event_threshold`, cited through the bridge; the source's `c_L > 0` form
  is recovered by discharging `0 < c_L + h_L` from (a) (`perQ_threshold`); `c_L ≤ 0` is the
  comply-regardless branch (`perQ_comply_of_gain_nonpos`). N+: the four-world instance of
  legitimacy.md R5.4 / check E2 (`e2_witness` for the inherited Setting-S rule; `e2_legit_*`
  for the full per-`Q` package: target `Q = δ_{(L,b)}`, `IsOptimal`, `ValueLegit`, `FunLegit`,
  the verdicts obtained *through* `perQ_threshold`).
* **(c) L.** Under function-form legitimacy the post-push credence is the legitimacy-weighted
  mixture `P k = P(E_Q ∧ L) Q + P k 𝟙_{Lᶜ}` (`funLegit_split`); literal adoption iff `ℓ = 1`
  (`funLegit_endorsed_iff`; on the full algebra the source's second disjunct is vacuous — a
  finding). Instance: `e2_not_endorsed` (`ℓ = 4/5 < 1`, function-form legitimacy without
  literal adoption).
* **(d) L.** Homogeneity: the sign of the push expectation, optimality and the threshold are
  invariant under `V ↦ λ • V`, `λ > 0` (`pushExpect_smul_nonpos_iff`, `isOptimal_smul_iff`,
  `complianceThreshold_smul`); the band is `corr-three-step`'s `twoState_band_iff` (cited).
* **(e) N+ (load-bearing, CE1).** Correctness is not a legitimacy event: in Example A with
  `X = X_{Q,plan₁} = (12, −12, 0)` and `W = {θ₂}`, under both kernels `¬ FunLegit` and
  `¬ ValueLegit` (`ce1_*`); substituting `W` for `L` reproduces T3(b) term for term
  (`pressExpectOn_W_eq`, `pressExpectOn_compl_W_eq_R`).

Sources: [[general-object-final]] S3(a)–(e), P4, R3, CE1; [[legitimacy-general-final]] Stmt 4(d),
Y2; legitimacy.md R5.4; [[corr-wf14b-inventory]] 005; [[corr-wf14-inventory]] 035.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A]

/-! ## (a) the harm stake is read off the target -/

/-- **`h_L(Q,a) = E_Q[V πQ − V a] ≥ 0`**, from `Q`-optimality of `πQ` alone: the harm stake needs
no kernel. (`IsOptimal Q V πQ` instantiated at `b = a` is the conclusion: kind L, audit r1 B2.)
Source: [[general-object-final]] S3(a), P4 ("`≤ 0` by `Q`-optimality of `π^Q`")
Kind: L
Fidelity: exact
Hyps: (a) `hπQ : IsOptimal Q V πQ` (the named optimal action) -/
theorem harm_nonneg_of_isOptimal (Q : Distr Ω) (V : A → Ω → ℝ) {πQ : A} (hπQ : IsOptimal Q V πQ)
    (a : A) : 0 ≤ expect Q (V πQ - V a) ∧ expect Q (devVar V πQ a) ≤ 0 := by
  have h := hπQ a
  rw [expect_sub']
  refine ⟨by linarith, ?_⟩
  have : devVar V πQ a = V a - V πQ := by funext ω; rfl
  rw [this, expect_sub']
  linarith

/-- **Under value-form legitimacy the push-and-`L` expectation of `X_{Q,a}` is nonpositive**:
`∑_{ω ∈ L} P k X_{Q,a} = P(E_Q ∧ L) · E_Q[X_{Q,a}] ≤ 0` (the `ValueLegit` rewrite composed with
`harm_nonneg_of_isOptimal`: kind L).
Source: [[general-object-final]] S3(a), P4
Kind: L
Fidelity: exact
Hyps: (a) `hπQ`, `ValueLegit P k Q L (devVar V πQ a)`, `k ≥ 0` -/
theorem pushExpectOn_nonpos_of_valueLegit (P : Distr Ω) {k : Ω → ℝ} (hk : ∀ ω, 0 ≤ k ω)
    (Q : Distr Ω) (V : A → Ω → ℝ) {πQ : A} (hπQ : IsOptimal Q V πQ) (a : A) (L : Finset Ω)
    (hV : ValueLegit P k Q L (devVar V πQ a)) :
    ∑ ω ∈ L, P.mass ω * k ω * devVar V πQ a ω ≤ 0 := by
  unfold ValueLegit at hV
  rw [hV]
  exact mul_nonpos_of_nonneg_of_nonpos (sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hk ω))
    (harm_nonneg_of_isOptimal Q V hπQ a).2

/-- **`h_L` through the bridge**: under `0 < P(E_Q ∧ L)` and value-form legitimacy,
`corr-three-step`'s `harmOn () L X_{Q,a}` *is* `E_Q[V πQ − V a]` — the harm stake is
target-determined, kernel-free. The hypothesis `ValueLegit` unfolds to
`∑_L P k X = P(E_Q ∧ L) · E_Q[X]` and the conclusion is that equation divided by the guard and
negated: the theorem is D11's definition read on the harm stake (the source's own first equality
in S3(a)), kind L, not P (audit r1, both lenses). What makes it load-bearing is the pair of
witnesses: `ce1_witness` (correctness `W` is *not* such an `L`) and `e2_legit_witness` (a proper
`L` with `ℓ ∈ (0,1)` *is*, and `h_L = 1` comes out of this theorem).
Source: [[general-object-final]] S3(a) ("`h_L(Q,a) = … = E_Q[V(·,π^Q) − V(·,a)]`")
Kind: L
Fidelity: exact
Hyps: (a) the positivity guard, `ValueLegit` -/
theorem harmOn_eq_of_valueLegit (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (Q : Distr Ω)
    (V : A → Ω → ℝ) (Sh : Finset A) (h1 : Sh.Nonempty) (h2 : Shᶜ.Nonempty) (πQ a : A)
    (L : Finset Ω) (hL : 0 < ∑ ω ∈ L, P.mass ω * k ω)
    (hV : ValueLegit P k Q L (devVar V πQ a)) :
    (toThreeStep P k hk V Sh h1 h2).harmOn () L (devVar V πQ a) = expect Q (V πQ - V a) := by
  unfold ThreeStep.harmOn
  rw [toThreeStep_pressExpectOn, toThreeStep_pressMassOn]
  unfold ValueLegit at hV
  rw [hV, mul_div_cancel_left₀ _ hL.ne']
  have : devVar V πQ a = V a - V πQ := by funext ω; rfl
  rw [this, expect_sub', expect_sub']
  ring

/-- **`h_L ≥ 0` is a theorem** under value-form legitimacy (not a hypothesis, as the source
stresses) — the two definitional unfoldings above composed (kind L).
Source: [[general-object-final]] S3(a) ("under minimal viability `h_L ≥ 0` is a theorem")
Kind: L
Fidelity: exact
Hyps: (a) `hπQ`, the guard, `ValueLegit` -/
theorem harmOn_nonneg_of_valueLegit (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (Q : Distr Ω)
    (V : A → Ω → ℝ) (Sh : Finset A) (h1 : Sh.Nonempty) (h2 : Shᶜ.Nonempty) {πQ : A}
    (hπQ : IsOptimal Q V πQ) (a : A) (L : Finset Ω) (hL : 0 < ∑ ω ∈ L, P.mass ω * k ω)
    (hV : ValueLegit P k Q L (devVar V πQ a)) :
    0 ≤ (toThreeStep P k hk V Sh h1 h2).harmOn () L (devVar V πQ a) := by
  rw [harmOn_eq_of_valueLegit P hk Q V Sh h1 h2 πQ a L hL hV]
  exact (harm_nonneg_of_isOptimal Q V hπQ a).1

/-! ## (b) the rule and the threshold, through the bridge -/

/-- The one-line discharge: `c_L > 0` and `h_L ≥ 0` give `0 < c_L + h_L`, so the source's
threshold form (stated with `c_L > 0`) is `corr-three-step`'s (stated with `0 < c_L + h_L`).
Source: mandate T4(b)
Kind: L
Fidelity: exact -/
theorem stakes_pos_of_gain_pos {c h : ℝ} (hc : 0 < c) (hh : 0 ≤ h) : 0 < c + h := by linarith

/-- **The rule** `E[X_{Q,a} | E_Q] = −ℓ h_L + (1−ℓ) c_L` (S3(b)), cited through the bridge.
Source: [[general-object-final]] S3(b); `corr-three-step` `condExpPress_eq_event_split`
Kind: L
Fidelity: exact
Hyps: (a) the two positive masses -/
theorem perQ_rule (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (V : A → Ω → ℝ) (Sh : Finset A)
    (h1 : Sh.Nonempty) (h2 : Shᶜ.Nonempty) (X : Ω → ℝ) (L : Finset Ω)
    (hL : 0 < ∑ ω ∈ L, P.mass ω * k ω) (hLc : 0 < ∑ ω ∈ Lᶜ, P.mass ω * k ω) :
    pushExpect P k X / pushMass P k =
      -(toThreeStep P k hk V Sh h1 h2).pressFracOn () L *
          (toThreeStep P k hk V Sh h1 h2).harmOn () L X +
        (1 - (toThreeStep P k hk V Sh h1 h2).pressFracOn () L) *
          (toThreeStep P k hk V Sh h1 h2).gainOn () L X := by
  rw [← toThreeStep_condExpPress P hk V Sh h1 h2]
  exact (toThreeStep P k hk V Sh h1 h2).condExpPress_eq_event_split () L X
    (by rw [toThreeStep_pressMassOn]; exact hL) (by rw [toThreeStep_pressMassOn]; exact hLc)

/-- **The threshold in the source's form** (S3(b), `c_L > 0` case): under value-form legitimacy
for `X_{Q,a}` (so `h_L = E_Q[V πQ − V a] ≥ 0`) and `c_L > 0`, comply iff
`c_L/(c_L + h_L) ≤ ℓ` — `belowThresholdIneq_iff_event_threshold` with its `0 < c_L + h_L`
discharged by (a).
Source: [[general-object-final]] S3(b) (v3 §1.2's formula, exact per alternative);
`corr-three-step` `belowThresholdIneq_iff_event_threshold`
Kind: C
Fidelity: exact
Hyps: (a) `hπQ`, `ValueLegit`, the two positive masses, `0 < c_L` -/
theorem perQ_threshold (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (Q : Distr Ω)
    (V : A → Ω → ℝ) (Sh : Finset A) (h1 : Sh.Nonempty) (h2 : Shᶜ.Nonempty) {πQ : A}
    (hπQ : IsOptimal Q V πQ) (a : A) (L : Finset Ω) (hL : 0 < ∑ ω ∈ L, P.mass ω * k ω)
    (hLc : 0 < ∑ ω ∈ Lᶜ, P.mass ω * k ω) (hV : ValueLegit P k Q L (devVar V πQ a))
    (hc : 0 < (toThreeStep P k hk V Sh h1 h2).gainOn () L (devVar V πQ a)) :
    pushExpect P k (devVar V πQ a) ≤ 0 ↔
      complianceThreshold ((toThreeStep P k hk V Sh h1 h2).gainOn () L (devVar V πQ a))
          (expect Q (V πQ - V a)) ≤
        (toThreeStep P k hk V Sh h1 h2).pressFracOn () L := by
  rw [← harmOn_eq_of_valueLegit P hk Q V Sh h1 h2 πQ a L hL hV,
    ← toThreeStep_belowThresholdIneq P hk V Sh h1 h2]
  exact (toThreeStep P k hk V Sh h1 h2).belowThresholdIneq_iff_event_threshold () L _
    (by rw [toThreeStep_pressMassOn]; exact hL) (by rw [toThreeStep_pressMassOn]; exact hLc)
    (stakes_pos_of_gain_pos hc (harmOn_nonneg_of_valueLegit P hk Q V Sh h1 h2 hπQ a L hL hV))

/-- **The `c_L ≤ 0` branch**: the illegitimate branch happens to recommend the better action in
expectation — comply whatever `ℓ` (with `h_L ≥ 0` from (a)).
Source: [[general-object-final]] S3(b) (last case); `corr-three-step` `belowThresholdIneq_of_gain_nonpos`
Kind: C
Fidelity: exact
Hyps: (a) `hπQ`, `ValueLegit`, the two positive masses, `c_L ≤ 0` -/
theorem perQ_comply_of_gain_nonpos (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k) (Q : Distr Ω)
    (V : A → Ω → ℝ) (Sh : Finset A) (h1 : Sh.Nonempty) (h2 : Shᶜ.Nonempty) {πQ : A}
    (hπQ : IsOptimal Q V πQ) (a : A) (L : Finset Ω) (hL : 0 < ∑ ω ∈ L, P.mass ω * k ω)
    (hLc : 0 < ∑ ω ∈ Lᶜ, P.mass ω * k ω) (hV : ValueLegit P k Q L (devVar V πQ a))
    (hc : (toThreeStep P k hk V Sh h1 h2).gainOn () L (devVar V πQ a) ≤ 0) :
    pushExpect P k (devVar V πQ a) ≤ 0 := by
  rw [← toThreeStep_belowThresholdIneq P hk V Sh h1 h2]
  exact (toThreeStep P k hk V Sh h1 h2).belowThresholdIneq_of_gain_nonpos () L _
    (by rw [toThreeStep_pressMassOn]; exact hL) (by rw [toThreeStep_pressMassOn]; exact hLc) hc
    (harmOn_nonneg_of_valueLegit P hk Q V Sh h1 h2 hπQ a L hL hV)

/-! ## (c) the bridge to adoption -/

/-- **Under function-form legitimacy the post-push credence is the legitimacy-weighted mixture**
`P ω k ω = P(E_Q ∧ L) · Q ω + P ω k ω 𝟙_{Lᶜ} ω` — `Q̂ = ℓ Q + (1−ℓ) P(· | E_Q, Lᶜ)` in
product form.
Source: [[general-object-final]] S3(d), P4 (bridge)
Kind: L
Fidelity: exact (product form) -/
theorem funLegit_split (P : Distr Ω) (k : Ω → ℝ) (Q : Distr Ω) (L : Finset Ω)
    (hF : FunLegit P k Q L) :
    ∀ ω, P.mass ω * k ω = (∑ ω ∈ L, P.mass ω * k ω) * Q.mass ω +
      (if ω ∈ L then 0 else P.mass ω * k ω) := by
  intro ω
  have := hF ω
  by_cases hω : ω ∈ L
  · simp only [hω, if_true] at this ⊢; linarith
  · simp only [hω, if_false] at this ⊢; linarith

/-- **Literal adoption under function-form legitimacy iff `ℓ = 1`** (on the full algebra): with
`0 < P(E_Q ∧ L)`, `Endorsed P k Q ↔ P(E_Q ∧ Lᶜ) = 0`. The source's second disjunct ("or the
illegitimate branch agrees with `Q`") is vacuous here: function-form legitimacy on the full
algebra puts `Q` inside `L`, and the `Lᶜ`-branch is supported off `L`; the disjunct has content
only on a coarser algebra (the source's `Θ`-marginal) — recorded in the findings.
Source: [[general-object-final]] S3(d) ("literal adoption iff `ℓ = 1` or the illegitimate branch
agrees with `Q`")
Kind: L
Fidelity: variant: full-algebra function form, where the second disjunct collapses
Hyps: (a) `FunLegit`, the guard, `k ≥ 0` -/
theorem funLegit_endorsed_iff (P : Distr Ω) {k : Ω → ℝ} (hk : ∀ ω, 0 ≤ k ω) (Q : Distr Ω)
    (L : Finset Ω) (hF : FunLegit P k Q L) (hL : 0 < ∑ ω ∈ L, P.mass ω * k ω) :
    Endorsed P k Q ↔ ∑ ω ∈ Lᶜ, P.mass ω * k ω = 0 := by
  have hsplit : pushMass P k = (∑ ω ∈ L, P.mass ω * k ω) + ∑ ω ∈ Lᶜ, P.mass ω * k ω :=
    (sum_add_sum_compl L _).symm
  constructor
  · intro hE
    apply le_antisymm _ (sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hk ω))
    apply sum_nonpos
    intro ω hω
    rw [mem_compl] at hω
    have h1 := hF ω
    simp only [hω, if_false] at h1
    have hQ : Q.mass ω = 0 := by
      rcases mul_eq_zero.1 h1.symm with h0 | h0
      · exact absurd h0 hL.ne'
      · exact h0
    rw [hE ω, hQ, mul_zero]
  · intro hLc ω
    rw [hsplit, hLc, add_zero]
    have h1 := hF ω
    by_cases hω : ω ∈ L
    · simpa [hω] using h1
    · have hzero : P.mass ω * k ω = 0 :=
        (sum_eq_zero_iff_of_nonneg fun ω' _ => mul_nonneg (P.nonneg ω') (hk ω')).1 hLc ω
          (mem_compl.2 hω)
      simp only [hω, if_false] at h1
      rw [hzero, h1]

/-! ## (d) homogeneity -/

/-- The sign of the push expectation is invariant under positive scaling of the variable.
Source: [[legitimacy-general-final]] Stmt 4(d) (homogeneity of degree zero); mandate T4(d)
Kind: L
Fidelity: exact -/
theorem pushExpect_smul_nonpos_iff (P : Distr Ω) (k : Ω → ℝ) {c : ℝ} (hc : 0 < c) (X : Ω → ℝ) :
    pushExpect P k (c • X) ≤ 0 ↔ pushExpect P k X ≤ 0 := by
  rw [pushExpect_smul]
  constructor
  · intro h
    by_contra hx
    push Not at hx
    linarith [mul_pos hc hx]
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hc.le h

/-- Optimality is invariant under positive scaling of the menu.
Source: mandate T4(d)
Kind: L
Fidelity: exact -/
theorem isOptimal_smul_iff (Q : Distr Ω) (V : A → Ω → ℝ) {c : ℝ} (hc : 0 < c) (a : A) :
    IsOptimal Q (fun b => c • V b) a ↔ IsOptimal Q V a := by
  unfold IsOptimal
  simp only [expect_smul]
  constructor
  · intro h b; exact le_of_mul_le_mul_left (h b) hc
  · intro h b; exact mul_le_mul_of_nonneg_left (h b) hc.le

/-- The compliance threshold is homogeneous of degree zero in the stakes.
Source: [[legitimacy-general-final]] Stmt 4(d), X2 (`90/91` at `(1,4)` and `(1000,4000)`)
Kind: L
Fidelity: exact -/
theorem complianceThreshold_smul {c h l : ℝ} (hl : l ≠ 0) :
    complianceThreshold (l * c) (l * h) = complianceThreshold c h := by
  unfold complianceThreshold
  rw [← mul_add, mul_div_mul_left _ _ hl]

/-! ## (b) N+: the four-world instance (legitimacy.md R5.4 / check E2) -/

/-- The four-world prior `(pL/2, pL/2, (1−pL)/2, (1−pL)/2)` on worlds `(L,g), (L,b), (¬L,g), (¬L,b)`.
Source: legitimacy.md R5.4 / `legitimacy-scratch/checks.py` E2. Kind: D. Fidelity: exact -/
def e2P (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) : Distr (Fin 4) where
  mass := ![pL/2, pL/2, (1 - pL)/2, (1 - pL)/2]
  nonneg i := by fin_cases i <;> simp <;> linarith
  sum_eq_one := by simp [Fin.sum_univ_four]; ring

/-- E2's press: the overseers track `X` on `L` and anti-track on `¬L`, so the press event is
`{(L,b), (¬L,g)}` (the expert's `E(X) ≤ 0` cells). The press event is *transcribed* from
checks.py E2's expert rows `(9/10,1/10,0,0)`, `(1/10,9/10,0,0)`, `(0,0,1/10,9/10)`,
`(0,0,9/10,1/10)` and its rule "press iff the expert's `E(X) ≤ 0`"; the four-world expert frame
itself is not formalized here (audit r1 fidelity 3.6).
Source: checks.py E2. Kind: D. Fidelity: exact (press event transcribed; frame not built) -/
def e2Press : Finset (Fin 4) := {1, 2}

/-- E2's variable `X = (1, −1, 1, −1)`. Source: checks.py E2. Kind: D. Fidelity: exact -/
def e2X : Fin 4 → ℝ := ![1, -1, 1, -1]

/-- E2's legitimacy event `L = {(L,g), (L,b)}`. Source: checks.py E2. Kind: D. Fidelity: exact -/
def e2L : Finset (Fin 4) := {0, 1}

/-- The complement of E2's legitimacy event. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e2L_compl : e2Lᶜ = {2, 3} := by decide

/-- The menu of the E2 instance: `cont = 0` with value `e2X`, `stop = 1` with value `0`.
Source: checks.py E2. Kind: D. Fidelity: exact -/
def e2V : Fin 2 → Fin 4 → ℝ := ![e2X, fun _ => 0]

/-- The E2 bridge: the four-world instance as a `ThreeStep` with `Sh = {stop}` on the menu
`{cont, stop}` (`V cont = X`, `V stop = 0`). Source: checks.py E2. Kind: D. Fidelity: exact -/
def e2S (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) : ThreeStep (Fin 4) Unit (Fin 2) :=
  toThreeStep (e2P pL h0 h1) (ind e2Press) (isKernel_ind _) e2V {1}
    (singleton_nonempty _) ⟨0, by decide⟩

/-- **N+ for T4(b)** (corr-wf14-035): in the four-world frame the stakes are `c' = 1`, `h' = 1`,
the threshold is `1/2`, and `ℓ = P(L | Pr) = pL`; the press is obeyed at `pL = 4/5`
(`E[X | Pr] = −3/5`) and overruled at `pL = 2/5` (`+1/5`).
Source: legitimacy.md R5.4 ("obeyed at legitimacy prior `0.8` … overruled at `0.4`"), checks.py E2
Kind: N+
Fidelity: exact (weights reconstructed from the script; both reported values reproduced)
Hyps: (a) none -/
theorem e2_witness :
    (e2S (4/5) (by norm_num) (by norm_num)).gainOn () e2L e2X = 1 ∧
      (e2S (4/5) (by norm_num) (by norm_num)).harmOn () e2L e2X = 1 ∧
      (e2S (4/5) (by norm_num) (by norm_num)).pressFracOn () e2L = 4/5 ∧
      (e2S (2/5) (by norm_num) (by norm_num)).pressFracOn () e2L = 2/5 ∧
      complianceThreshold (1 : ℝ) 1 = 1/2 ∧
      pushExpect (e2P (4/5) (by norm_num) (by norm_num)) (ind e2Press) e2X /
          pushMass (e2P (4/5) (by norm_num) (by norm_num)) (ind e2Press) = -3/5 ∧
      pushExpect (e2P (2/5) (by norm_num) (by norm_num)) (ind e2Press) e2X /
          pushMass (e2P (2/5) (by norm_num) (by norm_num)) (ind e2Press) = 1/5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ThreeStep.gainOn e2S
    rw [toThreeStep_pressExpectOn, toThreeStep_pressMassOn, e2L_compl]
    simp [e2P, e2Press, e2X, ind, Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair] <;> norm_num
  · unfold ThreeStep.harmOn e2S
    rw [toThreeStep_pressExpectOn, toThreeStep_pressMassOn]
    simp [e2P, e2L, e2Press, e2X, ind, Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair] <;> norm_num
  · unfold ThreeStep.pressFracOn e2S
    rw [toThreeStep_pressMassOn, toThreeStep_pressMass]
    simp [e2P, e2L, e2Press, pushMass, ind, Cleanroom.Found.LitDdbFrames.ind, Fin.sum_univ_four,
      Finset.sum_pair] <;> norm_num
  · unfold ThreeStep.pressFracOn e2S
    rw [toThreeStep_pressMassOn, toThreeStep_pressMass]
    simp [e2P, e2L, e2Press, pushMass, ind, Cleanroom.Found.LitDdbFrames.ind, Fin.sum_univ_four,
      Finset.sum_pair] <;> norm_num
  · unfold complianceThreshold; norm_num
  · simp [pushExpect, pushMass, e2P, e2Press, e2X, ind, Cleanroom.Found.LitDdbFrames.ind,
      Fin.sum_univ_four] <;> norm_num
  · simp [pushExpect, pushMass, e2P, e2Press, e2X, ind, Cleanroom.Found.LitDdbFrames.ind,
      Fin.sum_univ_four] <;> norm_num

/-! ## (a)–(c) N+: the full per-`Q` legitimacy package is inhabited (audit r1 B1)

`e2_witness` above checks the *inherited* Setting-S rule only (no target, no `ValueLegit`). The
instance below completes E2 with the target `Q = δ_{(L,b)}` on the menu `{cont, stop}`
(`πQ = stop`, `a = cont`, so `X_{Q,cont} = e2X`): `πQ` is `Q`-optimal, `ValueLegit` and
`FunLegit` hold for the proper event `L = {(L,g), (L,b)}` with `ℓ = pL ∈ (0,1)`, the guards and
`0 < c_L` hold, and the compliance verdicts are obtained *through* `perQ_threshold`;
`harmOn_eq_of_valueLegit` instantiates with `h_L = 1` and `funLegit_endorsed_iff` with
`ℓ = 4/5 < 1` (function-form legitimacy without literal adoption). Instance supplied by the
round-1 adversarial audit (`audit-r1-probes/ValueLegitWitness.lean`). -/

/-- The E2 target `Q = δ_{(L,b)}` (world `1`: legitimate and bad).
Source: checks.py E2 completed (audit r1 B1). Kind: D. Fidelity: exact -/
def e2Q : Distr (Fin 4) := Distr.delta 1

/-- On the E2 menu `X_{Q,cont} = e2X`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e2V_devVar : devVar e2V 1 0 = e2X := by
  funext ω; simp [devVar, e2V]

/-- `stop` is `Q`-optimal under `δ_{(L,b)}` (`E_Q[X] = −1 ≤ 0`).
Source: checks.py E2 completed. Kind: L. Fidelity: exact -/
theorem e2Q_optimal : IsOptimal e2Q e2V 1 := by
  intro b
  fin_cases b <;> simp [expect, e2Q, e2V, e2X, Distr.delta_mass, Fin.sum_univ_four] <;> norm_num

/-- `E_Q[V stop − V cont] = 1`. Source: checks.py E2 completed. Kind: L. Fidelity: exact -/
theorem e2Q_harm : expect e2Q (e2V 1 - e2V 0) = 1 := by
  simp [expect, e2Q, e2V, e2X, Distr.delta_mass, Fin.sum_univ_four]

/-- **`ValueLegit` holds for every `pL`**: `∑_L P k X = −pL/2 = (pL/2) · E_Q[X]`.
Source: [[general-object-final]] D11 on the E2 instance. Kind: L. Fidelity: exact -/
theorem e2_valueLegit (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) :
    ValueLegit (e2P pL h0 h1) (ind e2Press) e2Q e2L (devVar e2V 1 0) := by
  rw [e2V_devVar]
  unfold ValueLegit
  simp [e2P, e2L, e2Press, e2X, e2Q, Distr.delta_mass, expect, ind,
    Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair, Fin.sum_univ_four]

/-- **`FunLegit` holds for every `pL`**: `P k 𝟙_L = (pL/2) · δ_{(L,b)}`.
Source: [[general-object-final]] D11 on the E2 instance. Kind: L. Fidelity: exact -/
theorem e2_funLegit (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) :
    FunLegit (e2P pL h0 h1) (ind e2Press) e2Q e2L := by
  intro ω
  fin_cases ω <;> simp [e2P, e2L, e2Press, e2Q, Distr.delta_mass, ind,
    Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair]

/-- The two mass guards at `pL = 4/5` (`P(E_Q ∧ L) = 2/5`, `P(E_Q ∧ Lᶜ) = 1/10`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e2_guards_4_5 :
    0 < ∑ ω ∈ e2L, (e2P (4/5) (by norm_num) (by norm_num)).mass ω * ind e2Press ω ∧
      0 < ∑ ω ∈ e2Lᶜ, (e2P (4/5) (by norm_num) (by norm_num)).mass ω * ind e2Press ω := by
  constructor
  · simp [e2P, e2L, e2Press, ind, Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair] <;> norm_num
  · rw [e2L_compl]
    simp [e2P, e2Press, ind, Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair] <;> norm_num

/-- The two mass guards at `pL = 2/5` (`P(E_Q ∧ L) = 1/5`, `P(E_Q ∧ Lᶜ) = 3/10`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e2_guards_2_5 :
    0 < ∑ ω ∈ e2L, (e2P (2/5) (by norm_num) (by norm_num)).mass ω * ind e2Press ω ∧
      0 < ∑ ω ∈ e2Lᶜ, (e2P (2/5) (by norm_num) (by norm_num)).mass ω * ind e2Press ω := by
  constructor
  · simp [e2P, e2L, e2Press, ind, Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair] <;> norm_num
  · rw [e2L_compl]
    simp [e2P, e2Press, ind, Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair] <;> norm_num

/-- The gain stake of the E2 instance on `X_{Q,cont}` is `c_L = 1` for every `pL < 1`.
Source: checks.py E2. Kind: L. Fidelity: exact -/
theorem e2S_gain (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) (hlt : pL < 1) :
    (e2S pL h0 h1).gainOn () e2L (devVar e2V 1 0) = 1 := by
  rw [e2V_devVar]
  unfold ThreeStep.gainOn e2S
  rw [toThreeStep_pressExpectOn, toThreeStep_pressMassOn, e2L_compl]
  simp [e2P, e2Press, e2X, ind, Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair]
  have h2 : (1 : ℝ) - pL ≠ 0 := by intro h; linarith
  field_simp <;> exact h2

/-- The press-conditional legitimacy of the E2 instance is `ℓ = pL`.
Source: checks.py E2. Kind: L. Fidelity: exact -/
theorem e2S_frac (pL : ℝ) (h0 : 0 ≤ pL) (h1 : pL ≤ 1) :
    (e2S pL h0 h1).pressFracOn () e2L = pL := by
  unfold ThreeStep.pressFracOn e2S
  rw [toThreeStep_pressMassOn, toThreeStep_pressMass]
  simp [e2P, e2L, e2Press, pushMass, ind, Cleanroom.Found.LitDdbFrames.ind, Fin.sum_univ_four,
    Finset.sum_pair]
  ring

/-- **The full package of `perQ_threshold` is inhabited at `pL = 4/5`, and the verdict obtained
through it is "comply"** (`c_L/(c_L + h_L) = 1/2 ≤ ℓ = 4/5`).
Source: legitimacy.md R5.4 ("obeyed at legitimacy prior `0.8`"); audit r1 B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem e2_comply_via_perQ_threshold :
    pushExpect (e2P (4/5) (by norm_num) (by norm_num)) (ind e2Press) (devVar e2V 1 0) ≤ 0 := by
  have hc : 0 < (e2S (4/5) (by norm_num) (by norm_num)).gainOn () e2L (devVar e2V 1 0) := by
    rw [e2S_gain _ _ _ (by norm_num)]; norm_num
  have key := perQ_threshold (e2P (4/5) (by norm_num) (by norm_num)) (isKernel_ind e2Press) e2Q e2V
    {1} (singleton_nonempty _) ⟨0, by decide⟩ e2Q_optimal 0 e2L e2_guards_4_5.1 e2_guards_4_5.2
    (e2_valueLegit _ _ _) hc
  rw [key]
  show complianceThreshold ((e2S (4/5) _ _).gainOn () e2L (devVar e2V 1 0)) _ ≤
    (e2S (4/5) _ _).pressFracOn () e2L
  rw [e2S_gain _ _ _ (by norm_num), e2S_frac, e2Q_harm]
  unfold complianceThreshold; norm_num

/-- **… and at `pL = 2/5` the verdict obtained through it is "overrule"** (`1/2 ≤ 2/5` fails).
Source: legitimacy.md R5.4 ("overruled at `0.4`"); audit r1 B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem e2_overrule_via_perQ_threshold :
    ¬ pushExpect (e2P (2/5) (by norm_num) (by norm_num)) (ind e2Press) (devVar e2V 1 0) ≤ 0 := by
  have hc : 0 < (e2S (2/5) (by norm_num) (by norm_num)).gainOn () e2L (devVar e2V 1 0) := by
    rw [e2S_gain _ _ _ (by norm_num)]; norm_num
  have key := perQ_threshold (e2P (2/5) (by norm_num) (by norm_num)) (isKernel_ind e2Press) e2Q e2V
    {1} (singleton_nonempty _) ⟨0, by decide⟩ e2Q_optimal 0 e2L e2_guards_2_5.1 e2_guards_2_5.2
    (e2_valueLegit _ _ _) hc
  rw [key]
  show ¬ complianceThreshold ((e2S (2/5) _ _).gainOn () e2L (devVar e2V 1 0)) _ ≤
    (e2S (2/5) _ _).pressFracOn () e2L
  rw [e2S_gain _ _ _ (by norm_num), e2S_frac, e2Q_harm]
  unfold complianceThreshold; norm_num

/-- `harmOn_eq_of_valueLegit` instantiated: `h_L = E_Q[V stop − V cont] = 1`, kernel-free.
Source: [[general-object-final]] S3(a) on the E2 instance; audit r1 B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem e2_harmOn_via_theorem :
    (e2S (4/5) (by norm_num) (by norm_num)).harmOn () e2L (devVar e2V 1 0) = 1 := by
  unfold e2S
  rw [harmOn_eq_of_valueLegit _ (isKernel_ind e2Press) e2Q e2V {1} (singleton_nonempty _)
    ⟨0, by decide⟩ 1 0 e2L e2_guards_4_5.1 (e2_valueLegit _ _ _), e2Q_harm]

/-- `funLegit_endorsed_iff` instantiated: `ℓ = 4/5 < 1`, so the push is *not* endorsed —
function-form legitimacy without literal adoption (S3(d)'s first branch).
Source: [[general-object-final]] S3(d) on the E2 instance; audit r1 B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem e2_not_endorsed :
    ¬ Endorsed (e2P (4/5) (by norm_num) (by norm_num)) (ind e2Press) e2Q := by
  rw [funLegit_endorsed_iff _ (isKernel_ind e2Press).nonneg e2Q e2L (e2_funLegit _ _ _)
    e2_guards_4_5.1, e2L_compl]
  simp [e2P, e2Press, ind, Cleanroom.Found.LitDdbFrames.ind, Finset.sum_pair]
  norm_num

/-- **N+ for T4(a)(b)(c) as one package**: at `pL = 4/5` the target `δ_{(L,b)}` is distinct
from the prior, `stop` is `Q`-optimal, `L` is a proper event (`∅ ≠ L ≠ univ`) of legitimacy
`ℓ = 4/5 ∈ (0,1)`, both legitimacy forms hold, `h_L = 1` comes out of `harmOn_eq_of_valueLegit`,
the verdict through `perQ_threshold` is "comply" (and "overrule" at `2/5`), and the push is not
endorsed. Nothing here is a constant sequence, an empty type or a trivial event.
Source: legitimacy.md R5.4 / checks.py E2 completed with its target; audit r1 B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem e2_legit_witness :
    e2Q.mass ≠ (e2P (4/5) (by norm_num) (by norm_num)).mass ∧
      IsOptimal e2Q e2V 1 ∧
      e2L ≠ ∅ ∧ e2L ≠ univ ∧
      (e2S (4/5) (by norm_num) (by norm_num)).pressFracOn () e2L = 4/5 ∧
      ValueLegit (e2P (4/5) (by norm_num) (by norm_num)) (ind e2Press) e2Q e2L (devVar e2V 1 0) ∧
      FunLegit (e2P (4/5) (by norm_num) (by norm_num)) (ind e2Press) e2Q e2L ∧
      (e2S (4/5) (by norm_num) (by norm_num)).harmOn () e2L (devVar e2V 1 0) = 1 ∧
      pushExpect (e2P (4/5) (by norm_num) (by norm_num)) (ind e2Press) (devVar e2V 1 0) ≤ 0 ∧
      ¬ pushExpect (e2P (2/5) (by norm_num) (by norm_num)) (ind e2Press) (devVar e2V 1 0) ≤ 0 ∧
      ¬ Endorsed (e2P (4/5) (by norm_num) (by norm_num)) (ind e2Press) e2Q := by
  refine ⟨?_, e2Q_optimal, by decide, by decide, e2S_frac _ _ _, e2_valueLegit _ _ _,
    e2_funLegit _ _ _, e2_harmOn_via_theorem, e2_comply_via_perQ_threshold,
    e2_overrule_via_perQ_threshold, e2_not_endorsed⟩
  intro h
  have := congrFun h 0
  simp [e2Q, e2P, Distr.delta_mass] at this
  norm_num at this

/-! ## (e) CE1: correctness is not a legitimacy event -/

/-- Example A's `X_{Q,plan₁} = V plan₁ − V plan₂ = (12, −12, 0)`.
Source: [[general-object-final]] P12, CE1. Kind: L. Fidelity: exact -/
theorem exA_devVar_plan1 : devVar exA_V 1 0 = ![12, -12, 0] := by
  funext ω; fin_cases ω <;> simp [devVar, exA_V] <;> norm_num

/-- Example A's correctness event for `plan₁` is `W = {θ₂}`.
Source: [[general-object-final]] CE1. Kind: L. Fidelity: exact -/
theorem exA_Wset_plan1 : Wset exA_V 1 0 = {1} := by
  ext ω; fin_cases ω <;> simp [Wset, devVar, exA_V] <;> norm_num

/-- Example A's gain event for `plan₁` against `plan₂` is `R = {θ₁}`.
Source: [[general-object-final]] CE1, D6. Kind: L. Fidelity: exact -/
theorem exA_Rset_plan1 : Rset exA_V 1 0 = {0} := by
  ext ω; fin_cases ω <;> simp [Rset, devVar, exA_V] <;> norm_num

/-- **N+ for T3(b)'s odds form on Example A** (`πQ = plan₂`, `a = plan₁`, `R = {θ₁}`,
`W = {θ₂}`, `ε = 1/3`, `c = h = 12`, so the right-hand side is `(1/3)/(2/3) · 1 = 1/2`): under
`k₂ = (1/10, 3/5, 1/10)` the sensor odds are `α/β = (1/10)/(3/5) = 1/6 ≤ 1/2` and the verdict
obtained *through* `belowThreshold_iff_odds` is "comply" (`E[X 1_{E_Q}] = −6/5`); under
`k₃ = (1/2, 3/5, 1/2)` the odds are `5/6 > 1/2` and the verdict is "overrule" (`+6/5`). Both
guards of the odds form are inhabited (`P(E_Q ∧ R), P(E_Q ∧ W) > 0`).
Source: [[general-object-final]] S2(b), P3(b) on Example A; audit r1 adversarial 3.1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_odds_witness :
    sensorR exA_P exA_k2 exA_V 1 0 / sensorW exA_P exA_k2 exA_V 1 0 = 1/6 ∧
      sensorR exA_P exA_k3 exA_V 1 0 / sensorW exA_P exA_k3 exA_V 1 0 = 5/6 ∧
      (errRate exA_P exA_V 1 0 / (1 - errRate exA_P exA_V 1 0)) *
        (harmW exA_P exA_k2 exA_V 1 0 / gainR exA_P exA_k2 exA_V 1 0) = 1/2 ∧
      (errRate exA_P exA_V 1 0 / (1 - errRate exA_P exA_V 1 0)) *
        (harmW exA_P exA_k3 exA_V 1 0 / gainR exA_P exA_k3 exA_V 1 0) = 1/2 ∧
      pushExpect exA_P exA_k2 (devVar exA_V 1 0) ≤ 0 ∧
      ¬ pushExpect exA_P exA_k3 (devVar exA_V 1 0) ≤ 0 := by
  have hR2 : 0 < ∑ ω ∈ Rset exA_V 1 0, exA_P.mass ω * exA_k2 ω := by
    rw [exA_Rset_plan1]; simp [exA_P, exA_k2]
  have hW2 : 0 < ∑ ω ∈ Wset exA_V 1 0, exA_P.mass ω * exA_k2 ω := by
    rw [exA_Wset_plan1]; simp [exA_P, exA_k2]
  have hR3 : 0 < ∑ ω ∈ Rset exA_V 1 0, exA_P.mass ω * exA_k3 ω := by
    rw [exA_Rset_plan1]; simp [exA_P, exA_k3]
  have hW3 : 0 < ∑ ω ∈ Wset exA_V 1 0, exA_P.mass ω * exA_k3 ω := by
    rw [exA_Wset_plan1]; simp [exA_P, exA_k3]
  have hα2 : sensorR exA_P exA_k2 exA_V 1 0 / sensorW exA_P exA_k2 exA_V 1 0 = 1/6 := by
    unfold sensorR sensorW; rw [exA_Rset_plan1, exA_Wset_plan1]
    simp [exA_P, exA_k2]; norm_num
  have hα3 : sensorR exA_P exA_k3 exA_V 1 0 / sensorW exA_P exA_k3 exA_V 1 0 = 5/6 := by
    unfold sensorR sensorW; rw [exA_Rset_plan1, exA_Wset_plan1]
    simp [exA_P, exA_k3]; norm_num
  have hε : errRate exA_P exA_V 1 0 / (1 - errRate exA_P exA_V 1 0) = 1/2 := by
    unfold errRate; rw [exA_Rset_plan1, exA_Wset_plan1]
    simp [exA_P]; norm_num
  have hhc2 : harmW exA_P exA_k2 exA_V 1 0 / gainR exA_P exA_k2 exA_V 1 0 = 1 := by
    unfold harmW gainR; rw [exA_Rset_plan1, exA_Wset_plan1, exA_devVar_plan1]
    simp [exA_P, exA_k2]
  have hhc3 : harmW exA_P exA_k3 exA_V 1 0 / gainR exA_P exA_k3 exA_V 1 0 = 1 := by
    unfold harmW gainR; rw [exA_Rset_plan1, exA_Wset_plan1, exA_devVar_plan1]
    simp [exA_P, exA_k3]
  refine ⟨hα2, hα3, by rw [hε, hhc2]; norm_num, by rw [hε, hhc3]; norm_num, ?_, ?_⟩
  · rw [belowThreshold_iff_odds exA_P exA_kernels.2.1 exA_V 1 0 hR2 hW2, hα2, hε, hhc2]; norm_num
  · rw [belowThreshold_iff_odds exA_P exA_kernels.2.2.1 exA_V 1 0 hR3 hW3, hα3, hε, hhc3]; norm_num

/-- **N+ for T4(e), CE1 (load-bearing)**: correctness is not a legitimacy event. In Example A
with `W = {θ₂}`, under both kernels `k₁ = (1/6, 1, 1/3)` and `k₂ = (1/10, 3/5, 1/10)`:
`¬ FunLegit P k Q W` (the conditional on `W` is `(0, 1, 0) ≠ Q`) and
`¬ ValueLegit P k Q W X_{Q,plan₁}` (`E[X | E_Q, W] = −12 ≠ E_Q[X] = −24/5`).
Source: [[general-object-final]] D11, CE1, P4; [[corr-wf14b-inventory]] 005
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ce1_witness :
    (¬ FunLegit exA_P exA_k1 exA_Q (Wset exA_V 1 0)) ∧
      (¬ FunLegit exA_P exA_k2 exA_Q (Wset exA_V 1 0)) ∧
      (¬ ValueLegit exA_P exA_k1 exA_Q (Wset exA_V 1 0) (devVar exA_V 1 0)) ∧
      (¬ ValueLegit exA_P exA_k2 exA_Q (Wset exA_V 1 0) (devVar exA_V 1 0)) ∧
      expect exA_Q (devVar exA_V 1 0) = -24/5 := by
  rw [exA_Wset_plan1, exA_devVar_plan1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := h 1; simp [exA_P, exA_k1, exA_Q] at this <;> norm_num at this
  · intro h; have := h 1; simp [exA_P, exA_k2, exA_Q] at this <;> norm_num at this
  · intro h; unfold ValueLegit at h
    simp [exA_P, exA_k1, exA_Q, expect, Fin.sum_univ_three] at h <;> norm_num at h
  · intro h; unfold ValueLegit at h
    simp [exA_P, exA_k2, exA_Q, expect, Fin.sum_univ_three] at h <;> norm_num at h
  · simp [exA_Q, expect, Fin.sum_univ_three] <;> norm_num

/-- **Substituting `W` for `L` in (b) reproduces T3(b)**: the push-and-`W` expectation of
`X_{Q,a}` is the `W`-part of `pushExpect_devVar_split`, and the push-and-`Wᶜ` expectation is
the `R`-part (the `I` term vanishes) — so `h_L → h`, `c_L → c` term for term; the masses
differ by the indifferent worlds (`ℓ → P(W | E_Q, ¬I)`), as the source says.
Source: [[general-object-final]] S3(e), P4 ("correctness substitution")
Kind: L
Fidelity: exact -/
theorem pressExpectOn_compl_W_eq_R (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ a : A) :
    ∑ ω ∈ (Wset V πQ a)ᶜ, P.mass ω * k ω * devVar V πQ a ω =
      ∑ ω ∈ Rset V πQ a, P.mass ω * k ω * devVar V πQ a ω := by
  have hsplit := pushExpect_devVar_split P k V πQ a
  have htot : ∑ ω ∈ Wset V πQ a, P.mass ω * k ω * devVar V πQ a ω +
      ∑ ω ∈ (Wset V πQ a)ᶜ, P.mass ω * k ω * devVar V πQ a ω = pushExpect P k (devVar V πQ a) :=
    sum_add_sum_compl _ _
  linarith

end

end Cleanroom.Corrigibility.CorrGeneralObject
