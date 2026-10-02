import Cleanroom.Found.CorrThreeStep.TwoState

/-!
# The off-switch game: Wängberg et al.'s Theorem 9 and Corollary 10, and the bridge (T4)

Wängberg et al. 2017 analyse the off-switch game with a *two-type human*: given the sign of
`U_a`, the human is rational with probability `p_r⁺` (when `U_a ≥ 0`) or `p_r⁻` (when
`U_a < 0`) and anti-rational otherwise; a rational human allows `a` iff `U_a ≥ 0`, an
anti-rational one does the opposite. So the probability the human *allows* `a` is `p_r⁺` on
`{U_a ≥ 0}` and `1 − p_r⁻` on `{U_a < 0}` — `allowProb`. The five statistics are
`p_u⁻ = P(U_a < 0)`, `p_r⁺`, `p_r⁻`, `e_u⁺ = E[U_a | U_a ≥ 0]`, `e_u⁻ = E[U_a | U_a < 0]`.

From this semantics (a finite prior `μ` on worlds and `U : Ω → ℝ`) we **prove** Theorem 9's closed
forms `E[U | a] = p⁺e⁺ + p⁻e⁻` and `E[U | w(a)] = p⁺p_r⁺e⁺ + p⁻(1 − p_r⁻)e⁻` (with `E[U | s] = 0`
by normalisation), then Corollary 10: `a ≻ w(a)` iff expression (4), semantically
`p⁺(1 − p_r⁺)e⁺ + p⁻p_r⁻e⁻`, is positive, because `(4) = E[U | a] − E[U | w(a)]`. The printed
formula in the local pdftotext copy has jumbled superscripts; everything here is derived from
the semantics, not read off the printout.

**Bridge (T4, `variant`, ATTRIBUTION-UNVETTED mapping from `filler.md` F3):** on `twoState` with
`(p_u⁻, p_ar⁺, p_r⁻, e⁺, e⁻) = (ε, α, β, c, −h)` — i.e. `p_r⁺ = 1 − α`, `p_r⁻ = β` —
`allowProb = 1 − press`, `E[U | a] − E[U | w(a)] = −Δ₋`, so Corollary 10 reads `Δ₋ < 0`, and
Theorem 9's `E[U | w(a)] = Δ₊`.

Sources: `04-chai/wangberg-2017-…md` l. 262–282 (Theorem 9, Corollary 10);
`04-chai/hadfield-menell-2017-…md` l. 88–102 (Eq. 1); `filler.md` F3 (the mapping).
-/

namespace Cleanroom.Found.CorrThreeStep

open FactoredSpaces Finset ThreeStep

namespace OSG

variable {Ω : Type*} [Fintype Ω]

/-- `p_u⁺ = P(U ≥ 0)`. Source: Wängberg et al. 2017 §3 (statistics). Kind: D. Fidelity: exact -/
noncomputable def posMass (μ : Distr Ω) (U : Ω → ℝ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => 0 ≤ U ω), μ.mass ω

/-- `p_u⁻ = P(U < 0)`. Source: Wängberg et al. 2017 §3 (statistics). Kind: D. Fidelity: exact -/
noncomputable def negMass (μ : Distr Ω) (U : Ω → ℝ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => U ω < 0), μ.mass ω

/-- `E[U · 1_{U ≥ 0}] = p_u⁺ e_u⁺`. Source: Wängberg et al. 2017 §3. Kind: D. Fidelity: exact -/
noncomputable def posSum (μ : Distr Ω) (U : Ω → ℝ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => 0 ≤ U ω), μ.mass ω * U ω

/-- `E[U · 1_{U < 0}] = p_u⁻ e_u⁻`. Source: Wängberg et al. 2017 §3. Kind: D. Fidelity: exact -/
noncomputable def negSum (μ : Distr Ω) (U : Ω → ℝ) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω => U ω < 0), μ.mass ω * U ω

/-- `e_u⁺ = E[U | U ≥ 0]` (junk `0` when `P(U ≥ 0) = 0`; Theorem 9 below is stated so that the
junk value is harmless: `p⁺ e⁺ = E[U 1_{U≥0}]` holds in every case).
Source: Wängberg et al. 2017 §3. Kind: D. Fidelity: exact under `0 < posMass` -/
noncomputable def ePlus (μ : Distr Ω) (U : Ω → ℝ) : ℝ := posSum μ U / posMass μ U

/-- `e_u⁻ = E[U | U < 0]` (junk `0` when `P(U < 0) = 0`).
Source: Wängberg et al. 2017 §3. Kind: D. Fidelity: exact under `0 < negMass` -/
noncomputable def eMinus (μ : Distr Ω) (U : Ω → ℝ) : ℝ := negSum μ U / negMass μ U

/-- **The two-type human's allow probability**: `p_r⁺` where `U ≥ 0` (rational humans allow a
good action), `1 − p_r⁻` where `U < 0` (only anti-rational humans allow a bad one). This is the
off-switch game's `π^H` for Wängberg's human.
Source: Wängberg et al. 2017 §3.3 (the four subgames `G^±_r`, `G^±_ar`)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def allowProb (U : Ω → ℝ) (prPlus prMinus : ℝ) : Ω → ℝ :=
  fun ω => if 0 ≤ U ω then prPlus else 1 - prMinus

/-- `p · (s / p) = s` whenever `p = 0` forces `s = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma mul_div_self_of (p s : ℝ) (h : p = 0 → s = 0) : p * (s / p) = s := by
  by_cases hp : p = 0
  · rw [hp, h hp]; simp
  · field_simp

/-- If `P(U ≥ 0) = 0` then `E[U 1_{U ≥ 0}] = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma posSum_eq_zero_of_posMass_eq_zero (μ : Distr Ω) (U : Ω → ℝ) (h : posMass μ U = 0) :
    posSum μ U = 0 := by
  have hz := (sum_eq_zero_iff_of_nonneg fun ω _ => μ.nonneg ω).mp h
  exact sum_eq_zero fun ω hω => by rw [hz ω hω, zero_mul]

/-- If `P(U < 0) = 0` then `E[U 1_{U < 0}] = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma negSum_eq_zero_of_negMass_eq_zero (μ : Distr Ω) (U : Ω → ℝ) (h : negMass μ U = 0) :
    negSum μ U = 0 := by
  have hz := (sum_eq_zero_iff_of_nonneg fun ω _ => μ.nonneg ω).mp h
  exact sum_eq_zero fun ω hω => by rw [hz ω hω, zero_mul]

/-- `p⁺ e⁺ = E[U 1_{U ≥ 0}]` in every case. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma posMass_mul_ePlus (μ : Distr Ω) (U : Ω → ℝ) : posMass μ U * ePlus μ U = posSum μ U :=
  mul_div_self_of _ _ (posSum_eq_zero_of_posMass_eq_zero μ U)

/-- `p⁻ e⁻ = E[U 1_{U < 0}]` in every case. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma negMass_mul_eMinus (μ : Distr Ω) (U : Ω → ℝ) : negMass μ U * eMinus μ U = negSum μ U :=
  mul_div_self_of _ _ (negSum_eq_zero_of_negMass_eq_zero μ U)

/-- The filter `¬ 0 ≤ U ω` is the filter `U ω < 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma filter_not_nonneg (U : Ω → ℝ) :
    univ.filter (fun ω => ¬ 0 ≤ U ω) = univ.filter (fun ω => U ω < 0) :=
  filter_congr fun _ _ => not_le

/-- **Theorem 9, `E[U | a]`.** The prior expectation of `U` is `p_u⁺ e_u⁺ + p_u⁻ e_u⁻` (law of total
expectation over the sign of `U`).
Source: Wängberg et al. 2017 Theorem 9 (l. 262–270)
Kind: L (a sum split by the sign of `U`; relabelled from P in repair round 1 — the chain's content is the bridge)
Fidelity: exact
Hyps: (a) only -/
theorem expect_eq_stats (μ : Distr Ω) (U : Ω → ℝ) :
    expect μ U = posMass μ U * ePlus μ U + negMass μ U * eMinus μ U := by
  rw [posMass_mul_ePlus, negMass_mul_eMinus, expect, ← sum_filter_add_sum_filter_not univ (fun ω => 0 ≤ U ω),
    filter_not_nonneg]
  rfl

/-- **Theorem 9, `E[U | w(a)]`.** Under the two-type human, the expected value of deferring is
`p_u⁺ p_r⁺ e_u⁺ + p_u⁻ (1 − p_r⁻) e_u⁻`: the gain when `U ≥ 0` and the human (rationally)
allows, plus the loss when `U < 0` and the human (anti-rationally) allows.
Source: Wängberg et al. 2017 Theorem 9 (l. 262–270)
Kind: L (a sum split by the sign of `U`; relabelled from P in repair round 1 — the chain's content is the bridge)
Fidelity: exact
Hyps: (a) only -/
theorem expect_allow_eq_stats (μ : Distr Ω) (U : Ω → ℝ) (prPlus prMinus : ℝ) :
    expect μ (fun ω => allowProb U prPlus prMinus ω * U ω) =
      posMass μ U * prPlus * ePlus μ U + negMass μ U * (1 - prMinus) * eMinus μ U := by
  have e1 : posMass μ U * prPlus * ePlus μ U = prPlus * posSum μ U := by
    rw [← posMass_mul_ePlus]; ring
  have e2 : negMass μ U * (1 - prMinus) * eMinus μ U = (1 - prMinus) * negSum μ U := by
    rw [← negMass_mul_eMinus]; ring
  rw [e1, e2, expect, ← sum_filter_add_sum_filter_not univ (fun ω => 0 ≤ U ω), filter_not_nonneg]
  unfold posSum negSum
  rw [mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun ω hω => ?_
    rw [mem_filter] at hω
    simp only [allowProb, if_pos hω.2]
    ring
  · refine sum_congr rfl fun ω hω => ?_
    rw [mem_filter] at hω
    simp only [allowProb, if_neg (not_le.mpr hω.2)]
    ring

/-- **Expression (4) of Corollary 10**, semantically: `p_u⁺ p_ar⁺ e_u⁺ + p_u⁻ p_r⁻ e_u⁻` with
`p_ar⁺ = 1 − p_r⁺` — what `a` gains over `w(a)` when the human anti-rationally blocks a good
action (`p_u⁺ p_ar⁺ e_u⁺ ≥ 0`) plus what `a` loses to `w(a)` when the human rationally blocks a
bad one (`p_u⁻ p_r⁻ e_u⁻ ≤ 0`, as `e_u⁻ < 0`); the whole is `E[U | a] − E[U | w(a)]` (`expr4_eq`).
Source: Wängberg et al. 2017 Corollary 10 (l. 272–282; superscripts corrupted in the printout,
derived from the semantics)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def expr4 (μ : Distr Ω) (U : Ω → ℝ) (prPlus prMinus : ℝ) : ℝ :=
  posMass μ U * (1 - prPlus) * ePlus μ U + negMass μ U * prMinus * eMinus μ U

/-- **Corollary 10, the identity.** `(4) = E[U | a] − E[U | w(a)]`.
Source: Wängberg et al. 2017 Corollary 10 (proof's last line)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem expr4_eq (μ : Distr Ω) (U : Ω → ℝ) (prPlus prMinus : ℝ) :
    expr4 μ U prPlus prMinus =
      expect μ U - expect μ (fun ω => allowProb U prPlus prMinus ω * U ω) := by
  rw [expect_eq_stats, expect_allow_eq_stats, expr4]
  ring

/-- **Corollary 10.** Under the two-type human, `a` is strictly preferred to `w(a)` iff `(4) > 0`.
Source: Wängberg et al. 2017 Corollary 10
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem prefer_a_iff (μ : Distr Ω) (U : Ω → ℝ) (prPlus prMinus : ℝ) :
    expect μ (fun ω => allowProb U prPlus prMinus ω * U ω) < expect μ U ↔
      0 < expr4 μ U prPlus prMinus := by
  rw [expr4_eq]
  exact sub_pos.symm

end OSG

/-! ## The bridge to the two-state instance (T4) -/

section Bridge

open OSG

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- On `twoState` with `0 < c`, `0 < h`, Wängberg's allow probability with `p_r⁺ = 1 − α`,
`p_r⁻ = β` is the silence rate `1 − press`.
Source: [[corr-wf14-inventory]] 004 / filler.md F3 (the mapping; ATTRIBUTION-UNVETTED)
Kind: L
Fidelity: variant: the mapping is `filler`'s -/
lemma twoState_allowProb (hc : 0 < c) (hh : 0 < h) :
    allowProb ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) (1 - α) β =
      fun ω => 1 - (twoState ε α β c h hε hα hβ).press () ω := by
  funext ω
  cases ω
  · simp [allowProb, twoState, twoValue, twoPress, Xo, hc.le]
  · simp [allowProb, twoState, twoValue, twoPress, Xo, not_le.mpr (neg_neg_of_pos hh)]

/-- On `twoState` with `0 < c`, `0 < h`, expression (4) at `(p_r⁺, p_r⁻) = (1 − α, β)` equals
`(1 − ε)αc − εβh = −Δ₋`.
Source: [[corr-wf14-inventory]] 004 / filler.md F3 (the mapping; ATTRIBUTION-UNVETTED)
Kind: C
Fidelity: variant: the five-statistic mapping is `filler`'s
Hyps: (a) `0 < c`, `0 < h` place `right` in `{U ≥ 0}` and `wrong` in `{U < 0}` -/
theorem twoState_expr4 (hc : 0 < c) (hh : 0 < h) :
    expr4 (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) (1 - α) β =
      -(twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop := by
  have hμ : twoPoint ε hε = (twoState ε α β c h hε hα hβ).μ () := rfl
  rw [expr4_eq, twoState_allowProb ε α β c h hε hα hβ hc hh, deltaMinus, neg_neg, hμ]
  have hsil : expect ((twoState ε α β c h hε hα hβ).μ ())
      (fun ω => (1 - (twoState ε α β c h hε hα hβ).press () ω) *
        (twoState ε α β c h hε hα hβ).Xo () .press .cont .stop ω) =
      (twoState ε α β c h hε hα hβ).obsExpect () .silent
        ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) := by
    simp only [expect, obsExpect, obsWeight_silent]
    exact sum_congr rfl fun ω _ => by ring
  rw [hsil]
  have := (twoState ε α β c h hε hα hβ).obsExpect_press_add_silent ()
    ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop)
  linarith

/-- **Corollary 10 on the two-state instance**: `a ≻ w(a)` iff `Δ₋ < 0` — the off-switch game's
compliance verdict is the sign of `Δ₋`, i.e. desideratum 1's failure.
Source: [[corr-wf14-inventory]] 004 / filler.md F3 ("Corollary 10 is `Δ₋ ≥ 0` verbatim")
Kind: C
Fidelity: variant: via `filler`'s mapping
Hyps: (a) only -/
theorem twoState_prefer_a_iff (hc : 0 < c) (hh : 0 < h) :
    expect (twoPoint ε hε)
        (fun ω => allowProb ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) (1 - α) β ω *
          (twoState ε α β c h hε hα hβ).Xo () .press .cont .stop ω) <
      expect (twoPoint ε hε) ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) ↔
      (twoState ε α β c h hε hα hβ).deltaMinus () .cont .stop < 0 := by
  rw [prefer_a_iff, twoState_expr4 ε α β c h hε hα hβ hc hh]
  exact neg_pos

/-- **Theorem 9's `E[U | w(a)]` on the two-state instance is `Δ₊`** — the silence half Wängberg
et al. state but do not name.
Source: [[corr-wf14-inventory]] 004 / filler.md F3 (last sentence)
Kind: L (`twoState_allowProb` + `Xo_eq_of_A1` + one `sum_congr`; relabelled from C in repair round 2)
Fidelity: variant: via `filler`'s mapping
Hyps: (a) only -/
theorem twoState_expect_allow_eq_deltaPlus (hc : 0 < c) (hh : 0 < h) :
    expect (twoPoint ε hε)
        (fun ω => allowProb ((twoState ε α β c h hε hα hβ).Xo () .press .cont .stop) (1 - α) β ω *
          (twoState ε α β c h hε hα hβ).Xo () .press .cont .stop ω) =
      (twoState ε α β c h hε hα hβ).deltaPlus () .cont .stop := by
  have hμ : twoPoint ε hε = (twoState ε α β c h hε hα hβ).μ () := rfl
  rw [twoState_allowProb ε α β c h hε hα hβ hc hh, deltaPlus,
    ← Xo_eq_of_A1 _ (twoState_A1 ε α β c h hε hα hβ) () .press .silent, hμ]
  simp only [expect, obsExpect, obsWeight_silent]
  exact sum_congr rfl fun ω _ => by ring

end Bridge

end Cleanroom.Found.CorrThreeStep
