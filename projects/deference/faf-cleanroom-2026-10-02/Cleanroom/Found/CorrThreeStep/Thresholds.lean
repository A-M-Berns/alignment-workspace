import Cleanroom.Found.CorrThreeStep.Setting
import Mathlib.Tactic.FieldSimp

/-!
# Threshold forms on a general finite `Ω`

* **T5**: the compliance-threshold lemma `q·(−h) + (1 − q)·c ≤ 0 ↔ c/(c + h) ≤ q`.
* **T9(b)**: with an abstract event `L ⊆ Ω` (no theory of legitimacy here), the conditional
  expectation after a press splits as `−ℓ·h_L + (1 − ℓ)·c_L` (total expectation, three masses
  positive), so the below-threshold inequality is `(1 − ℓ)·c_L ≤ ℓ·h_L`, and for `c_L > 0` it is
  `c_L/(c_L + h_L) ≤ ℓ`. The source says this "is an identity with named hypotheses" and must not
  be read as more; it is recorded here as `L`.

Sources: position statement §2.13(a); `miri.md` I12.1; `general-object-final.md` S3(b), D10.
-/

namespace Cleanroom.Found.CorrThreeStep

open FactoredSpaces Finset

/-! ## T5 — the compliance threshold -/

/-- **T5.** For a decision with posterior probability `q` of being wrong, harm `h` when wrong
and gain `c` when right: continuing is weakly worse than stopping iff `q` is at least the
compliance threshold `c/(c + h)`. Needs only `0 < c + h` (so the source's `c, h > 0` is a
special case).
Source: [[corr-wf13-inventory]] 002 / position statement §2.13(a); miri.md I12.1
Kind: L
Fidelity: stronger: hypothesis weakened from `c, h > 0` to `0 < c + h`
Hyps: (a) none beyond the stated positivity -/
theorem complianceThreshold_iff (q c h : ℝ) (hch : 0 < c + h) :
    q * (-h) + (1 - q) * c ≤ 0 ↔ complianceThreshold c h ≤ q := by
  unfold complianceThreshold
  rw [div_le_iff₀ hch]
  have : q * (c + h) = q * c + q * h := by ring
  rw [this]
  constructor <;> intro H <;> linarith

/-- **T5, strict form.** Continuing is strictly worse than stopping iff `c/(c + h) < q`.
Source: [[corr-wf13-inventory]] 002 / position statement §2.13(a)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem complianceThreshold_lt_iff (q c h : ℝ) (hch : 0 < c + h) :
    q * (-h) + (1 - q) * c < 0 ↔ complianceThreshold c h < q := by
  unfold complianceThreshold
  rw [div_lt_iff₀ hch]
  have : q * (c + h) = q * c + q * h := by ring
  rw [this]
  constructor <;> intro H <;> linarith

/-! ## T9(b) — the per-`Q` rule's identity on an abstract event -/

namespace ThreeStep

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂]
variable (S : ThreeStep Ω A₁ A₂)

/-- The press-and-`L` mass `P(Pr ∧ L; a₁) = ∑ ω ∈ L, μ(ω) P(Pr|ω;a₁)`.
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md S3(b) (`P_t(L_Q ∣ E_Q)` times `P_t(E_Q)`)
Kind: D
Fidelity: exact -/
noncomputable def pressMassOn (a : A₁) (L : Finset Ω) : ℝ := ∑ ω ∈ L, (S.μ a).mass ω * S.press a ω

/-- The press-and-`L` expectation `E_P[X · 1_Pr · 1_L ; a₁]`.
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md D10 (the stakes' numerators)
Kind: D
Fidelity: exact -/
noncomputable def pressExpectOn (a : A₁) (L : Finset Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω ∈ L, (S.μ a).mass ω * S.press a ω * X ω

/-- `ℓ = P(L | Pr; a₁)`, the fraction of the press mass on the event `L` (derived; junk at
`pressMass = 0`). The source's `ℓ` is a legitimacy posterior; here `L` is an abstract event with
no theory of legitimacy behind it, hence the neutral name (mandate's naming discipline).
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md S3 (`ℓ := P_t(L_Q ∣ E_Q)`)
Kind: D
Fidelity: exact under `0 < pressMass` -/
noncomputable def pressFracOn (a : A₁) (L : Finset Ω) : ℝ := S.pressMassOn a L / S.pressMass a

/-- `h_L = −E_P[X | Pr ∧ L; a₁]`, the harm stake on `L` (derived; junk at `pressMassOn L = 0`).
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md D10 (`h_L`)
Kind: D
Fidelity: exact under `0 < pressMassOn a L` -/
noncomputable def harmOn (a : A₁) (L : Finset Ω) (X : Ω → ℝ) : ℝ :=
  -(S.pressExpectOn a L X / S.pressMassOn a L)

/-- `c_L = E_P[X | Pr ∧ Lᶜ; a₁]`, the gain stake off `L` (derived; junk at `pressMassOn Lᶜ = 0`).
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md D10 (`c_L`)
Kind: D
Fidelity: exact under `0 < pressMassOn a Lᶜ` -/
noncomputable def gainOn [DecidableEq Ω] (a : A₁) (L : Finset Ω) (X : Ω → ℝ) : ℝ :=
  S.pressExpectOn a Lᶜ X / S.pressMassOn a Lᶜ

/-- The press mass splits over `L` and `Lᶜ`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMassOn_add_compl [DecidableEq Ω] (a : A₁) (L : Finset Ω) :
    S.pressMassOn a L + S.pressMassOn a Lᶜ = S.pressMass a :=
  sum_add_sum_compl L _

/-- The press expectation splits over `L` and `Lᶜ`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressExpectOn_add_compl [DecidableEq Ω] (a : A₁) (L : Finset Ω) (X : Ω → ℝ) :
    S.pressExpectOn a L X + S.pressExpectOn a Lᶜ X = S.obsExpect a .press X := by
  unfold pressExpectOn obsExpect
  simp only [obsWeight_press]
  exact sum_add_sum_compl L _

/-- The press-and-`L` mass is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressMassOn_nonneg (a : A₁) (L : Finset Ω) : 0 ≤ S.pressMassOn a L :=
  sum_nonneg fun ω _ => mul_nonneg ((S.μ a).nonneg ω) (S.press_nonneg a ω)

/-- `ℓ ∈ [0, 1]` under `0 < pressMass`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma pressFracOn_mem_Icc [DecidableEq Ω] (a : A₁) (L : Finset Ω) (hpm : 0 < S.pressMass a) :
    S.pressFracOn a L ∈ Set.Icc (0 : ℝ) 1 := by
  unfold pressFracOn
  refine ⟨div_nonneg (S.pressMassOn_nonneg a L) hpm.le, ?_⟩
  rw [div_le_one hpm, ← S.pressMassOn_add_compl a L]
  linarith [S.pressMassOn_nonneg a Lᶜ]

/-- **T9(b), the identity.** With the press-and-`L` and press-and-`Lᶜ` masses positive (which
forces `0 < pressMass`, so that hypothesis is derived, not taken),
`E_P[X | Pr; a₁] = −ℓ·h_L + (1 − ℓ)·c_L` — total expectation over `L` and `Lᶜ`. "An identity
with named hypotheses", not a headline.
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md S3(b)
Kind: L
Fidelity: exact (restricted to Setting S: `L` is an abstract event, no reflection hypothesis)
Hyps: (a) the two positive masses name where the conditional forms are defined -/
theorem condExpPress_eq_event_split [DecidableEq Ω] (a : A₁) (L : Finset Ω) (X : Ω → ℝ)
    (hL : 0 < S.pressMassOn a L) (hLc : 0 < S.pressMassOn a Lᶜ) :
    S.condExpPress a X = -S.pressFracOn a L * S.harmOn a L X + (1 - S.pressFracOn a L) * S.gainOn a L X := by
  have hpm : 0 < S.pressMass a := by rw [← S.pressMassOn_add_compl a L]; linarith
  have h1 : 1 - S.pressFracOn a L = S.pressMassOn a Lᶜ / S.pressMass a := by
    rw [pressFracOn, eq_div_iff hpm.ne', sub_mul, div_mul_cancel₀ _ hpm.ne',
      ← S.pressMassOn_add_compl a L]
    ring
  rw [h1, condExpPress, ← S.pressExpectOn_add_compl a L X]
  unfold pressFracOn harmOn gainOn
  have := hpm.ne'
  have := hL.ne'
  have := hLc.ne'
  field_simp

/-- **T9(b), the rule.** Under the same two positive masses, the below-threshold inequality is
`(1 − ℓ)·c_L ≤ ℓ·h_L`.
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md S3(b)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem belowThresholdIneq_iff_event_split [DecidableEq Ω] (a : A₁) (L : Finset Ω) (X : Ω → ℝ)
    (hL : 0 < S.pressMassOn a L) (hLc : 0 < S.pressMassOn a Lᶜ) :
    S.belowThresholdIneq a X ↔ (1 - S.pressFracOn a L) * S.gainOn a L X ≤ S.pressFracOn a L * S.harmOn a L X := by
  have hpm : 0 < S.pressMass a := by rw [← S.pressMassOn_add_compl a L]; linarith
  rw [S.belowThresholdIneq_iff_condExpPress a X hpm, S.condExpPress_eq_event_split a L X hL hLc]
  constructor <;> intro H <;> linarith

/-- **T9(b), threshold form.** When `c_L + h_L > 0` (in particular when `c_L > 0` and `h_L ≥ 0`),
the below-threshold inequality is `c_L/(c_L + h_L) ≤ ℓ` — the corpus's "comply when
`P(L | pushed) ≥ c/(c + h)`" made exact per alternative.
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md S3(b); v3 §1.2 formula
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem belowThresholdIneq_iff_event_threshold [DecidableEq Ω] (a : A₁) (L : Finset Ω) (X : Ω → ℝ)
    (hL : 0 < S.pressMassOn a L) (hLc : 0 < S.pressMassOn a Lᶜ)
    (hstakes : 0 < S.gainOn a L X + S.harmOn a L X) :
    S.belowThresholdIneq a X ↔ complianceThreshold (S.gainOn a L X) (S.harmOn a L X) ≤ S.pressFracOn a L := by
  rw [S.belowThresholdIneq_iff_event_split a L X hL hLc, ← complianceThreshold_iff _ _ _ hstakes]
  constructor <;> intro H <;> linarith

/-- **T9(b), the degenerate branch.** When `c_L ≤ 0` and `0 ≤ h_L` (the illegitimate branch
happens to recommend the better action in expectation) the below-threshold inequality holds
whatever `ℓ`.
Source: [[corr-wf14b-inventory]] 005 / general-object-final.md S3(b) (last case)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem belowThresholdIneq_of_gain_nonpos [DecidableEq Ω] (a : A₁) (L : Finset Ω) (X : Ω → ℝ)
    (hL : 0 < S.pressMassOn a L) (hLc : 0 < S.pressMassOn a Lᶜ)
    (hc : S.gainOn a L X ≤ 0) (hh : 0 ≤ S.harmOn a L X) : S.belowThresholdIneq a X := by
  have hpm : 0 < S.pressMass a := by rw [← S.pressMassOn_add_compl a L]; linarith
  rw [S.belowThresholdIneq_iff_event_split a L X hL hLc]
  obtain ⟨h0, h1⟩ := S.pressFracOn_mem_Icc a L hpm
  nlinarith

end ThreeStep

end Cleanroom.Found.CorrThreeStep
