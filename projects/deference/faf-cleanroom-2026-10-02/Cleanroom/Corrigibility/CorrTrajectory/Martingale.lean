import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.BorelCantelli

/-!
# `corr-trajectory` — `Martingale`: Statement 8(b) in Layer M (T7, load-bearing 1)

Over Mathlib's `Supermartingale Z ℱ μ` on a probability space:

* **(i)** `∫ ∑_{t ≤ T} ℓ_t ∂μ ≤ ∫ Ψ_0 ∂μ` for `Z_t = Ψ_t + ∑_{s<t} ℓ_s` with `Ψ_{T+1} = 0`
  (`certificate_expectation`), and `≤ Ψ₀` when `Ψ_0` is the constant `Ψ₀` (`certificate_const`);
* **(ii) Ville's inequality** — Mathlib has none for supermartingales — by optional stopping on `−Z`
  with the hitting time `hittingBtwn Z {λ ≤ ·} 0 n` and Markov's inequality on the stopped value:
  `λ · μ.real {ω ∣ ∃ t ≤ n, λ ≤ Z_t ω} ≤ ∫ Z_0 ∂μ` (`ville`), hence the source's
  `P*(∃ t ≤ T, Z_t ≥ λ) ≤ Ψ₀/λ` (`ville_ratio`);
* the surviving neighbour of Statement 11(c): a nonnegative supermartingale converges a.s.
  (`ae_tendsto_of_nonneg`, from `Submartingale.ae_tendsto_limitProcess` on `−Z`);
* Statement 7(c′), Lévy's conditional Borel–Cantelli, cited from Mathlib (`levy_borel_cantelli`).

The Layer-F witnesses (A1, A8, A2, A3, C6) live in `LossToy`/`LegitToy`; without the T15 bridge each
refutation row says it refutes the Layer-F form of the claim, which is the sources' own (finite) form.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open MeasureTheory ProbabilityTheory Filter Topology Finset

namespace Martingale

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m}

/-- **The expectation of a supermartingale is non-increasing**: `∫ Z_n ≤ ∫ Z_0`.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md proof of Statement 8(b)
Kind: L (`Supermartingale.setIntegral_le` on `univ`)
Fidelity: exact -/
theorem integral_antitone {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (n : ℕ) :
    ∫ ω, Z n ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ := by
  have := hZ.setIntegral_le (Nat.zero_le n) (MeasurableSet.univ (m := ℱ 0))
  simpa [setIntegral_univ] using this

/-- **Statement 8(b)(i), Layer M**: for `Z_t = Ψ_t + ∑_{s<t} ℓ_s` a `P*`-supermartingale with
`Ψ_{T+1} = 0`, `∫ ∑_{t ≤ T} ℓ_t ∂μ ≤ ∫ Ψ_0 ∂μ`. The hypothesis is `Supermartingale Z ℱ μ` on all of
`ℕ`, while the source asks `Δ_t ≤ 0` only for `t ≤ T` with `Ψ` pinned at `T + 1`; padding
`Ψ_t = ℓ_t = 0` for `t > T` makes the two equivalent (audit r1, fidelity N3). No Layer-F instance is a
formal instance of this theorem (T15 not landed): it is unwitnessed, covered in principle only.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b) (first display)
Kind: C (`Supermartingale.setIntegral_le` between `0` and `T + 1`, then `Z_{T+1} = Reg_T`, `Z_0 = Ψ_0`; relabelled from P, audit r1 N1)
Fidelity: exact (up to the padding above)
Hyps: (a) `Supermartingale Z ℱ μ` is the named hypothesis (the source's `Δ_t ≤ 0`); `Ψ_{T+1} = 0` as in the source -/
theorem certificate_expectation (Ψ ℓ : ℕ → Ω → ℝ) (T : ℕ) (hΨT : ∀ ω, Ψ (T + 1) ω = 0)
    (hZ : Supermartingale (fun t ω => Ψ t ω + ∑ s ∈ range t, ℓ s ω) ℱ μ) :
    ∫ ω, (∑ t ∈ range (T + 1), ℓ t ω) ∂μ ≤ ∫ ω, Ψ 0 ω ∂μ := by
  have h := integral_antitone hZ (T + 1)
  simp only [hΨT, zero_add, range_zero, sum_empty, add_zero] at h
  exact h

/-- **Statement 8(f): the agent's own number.** With `Ψ_0 ≡ Ψ₀` constant, `∫ ∑_{t ≤ T} ℓ_t ∂μ ≤ Ψ₀`.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b), (f)
Kind: C
Fidelity: exact (the constant-`Ψ₀` form as a corollary; `ℱ 0 = ⊥` is not assumed globally)
Hyps: (a) only -/
theorem certificate_const (Ψ ℓ : ℕ → Ω → ℝ) (T : ℕ) (hΨT : ∀ ω, Ψ (T + 1) ω = 0) (psi0 : ℝ)
    (h0 : ∀ ω, Ψ 0 ω = psi0)
    (hZ : Supermartingale (fun t ω => Ψ t ω + ∑ s ∈ range t, ℓ s ω) ℱ μ) :
    ∫ ω, (∑ t ∈ range (T + 1), ℓ t ω) ∂μ ≤ psi0 := by
  have h := certificate_expectation Ψ ℓ T hΨT hZ
  have e : (fun ω => Ψ 0 ω) = fun _ => psi0 := funext h0
  rw [e] at h
  simpa [integral_const] using h

/-! ### Ville's inequality -/

/-- The hitting time of `{λ ≤ ·}` by `Z` within `[0, n]`, valued in `ℕ∞`.
Source: invariant-final.md Statement 8(b) (the excursion event). Kind: D. Fidelity: exact -/
noncomputable def hitTime (Z : ℕ → Ω → ℝ) (lam : ℝ) (n : ℕ) : Ω → ℕ∞ :=
  fun ω => ((hittingBtwn Z {y : ℝ | lam ≤ y} 0 n ω : ℕ) : ℕ∞)

/-- `hitTime_isStoppingTime` (supporting theorem). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem hitTime_isStoppingTime {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (lam : ℝ) (n : ℕ) :
    IsStoppingTime ℱ (hitTime Z lam n) :=
  hZ.1.adapted.isStoppingTime_hittingBtwn measurableSet_Ici

/-- `hitTime_le` (supporting theorem). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem hitTime_le {Z : ℕ → Ω → ℝ} (lam : ℝ) (n : ℕ) (ω : Ω) : hitTime Z lam n ω ≤ n := by
  unfold hitTime
  exact_mod_cast (hittingBtwn_le (u := Z) (s := {y : ℝ | lam ≤ y}) (n := 0) (m := n) ω)

/-- `∫ Z_τ ≤ ∫ Z_0` for the bounded stopping time `τ` (optional stopping on `−Z`).
Source: mandate "Two layers" (the route named there). Kind: C. Fidelity: exact -/
theorem integral_stoppedValue_le {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (lam : ℝ) (n : ℕ) :
    ∫ ω, stoppedValue Z (hitTime Z lam n) ω ∂μ ≤ ∫ ω, Z 0 ω ∂μ := by
  have hτ := hitTime_isStoppingTime hZ lam n
  have h0 : IsStoppingTime ℱ (fun _ : Ω => ((0 : ℕ) : ℕ∞)) := isStoppingTime_const ℱ (0 : ℕ)
  have hle : (fun _ : Ω => ((0 : ℕ) : ℕ∞)) ≤ hitTime Z lam n := fun ω => by simp
  have hos := hZ.neg.expected_stoppedValue_mono h0 hτ hle (N := n) (hitTime_le lam n)
  have e0 : stoppedValue (-Z) (fun _ : Ω => ((0 : ℕ) : ℕ∞)) = fun ω => -Z 0 ω := by
    funext ω
    show (-Z) (((0 : ℕ) : ℕ∞).untopA) ω = -Z 0 ω
    rfl
  have eτ : stoppedValue (-Z) (hitTime Z lam n) = fun ω => -stoppedValue Z (hitTime Z lam n) ω := by
    funext ω; simp [stoppedValue]
  rw [e0, eτ, integral_neg, integral_neg] at hos
  linarith

/-- The stopped value is integrable (bounded stopping time). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem integrable_stoppedValue {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (lam : ℝ) (n : ℕ) :
    Integrable (stoppedValue Z (hitTime Z lam n)) μ := by
  have := hZ.neg.integrable_stoppedValue (hitTime_isStoppingTime hZ lam n) (hitTime_le lam n)
  have e : stoppedValue (-Z) (hitTime Z lam n) = fun ω => -stoppedValue Z (hitTime Z lam n) ω := by
    funext ω; simp [stoppedValue]
  rw [e] at this
  simpa using this.neg

/-- On the excursion event the stopped value is `≥ λ`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem excursion_subset {Z : ℕ → Ω → ℝ} (lam : ℝ) (n : ℕ) :
    {ω | ∃ t ≤ n, lam ≤ Z t ω} ⊆ {ω | lam ≤ stoppedValue Z (hitTime Z lam n) ω} := by
  intro ω hω
  obtain ⟨t, ht, hlt⟩ := hω
  have h : ∃ j ∈ Set.Icc 0 n, Z j ω ∈ {y : ℝ | lam ≤ y} := ⟨t, ⟨Nat.zero_le t, ht⟩, hlt⟩
  have := stoppedValue_hittingBtwn_mem h
  show lam ≤ stoppedValue Z (hitTime Z lam n) ω
  exact this

/-- **Statement 8(b)(ii), Layer M: Ville's inequality for a nonnegative supermartingale.**
`λ · μ.real {ω ∣ ∃ t ≤ n, λ ≤ Z_t ω} ≤ ∫ Z_0 ∂μ`, by optional stopping on `−Z` at the hitting time
and Markov's inequality on the stopped value.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b) (second display, "Ville")
Kind: P (optional stopping + Markov; no Ville in Mathlib)
Fidelity: exact (real-valued form of the measure; the `ENNReal` form is `ville_ennreal`)
Hyps: (a) only -/
theorem ville {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (hnn : ∀ t ω, 0 ≤ Z t ω) (lam : ℝ) (n : ℕ) :
    lam * μ.real {ω | ∃ t ≤ n, lam ≤ Z t ω} ≤ ∫ ω, Z 0 ω ∂μ := by
  rcases le_or_gt lam 0 with hlam | hlam
  · have h1 : lam * μ.real {ω | ∃ t ≤ n, lam ≤ Z t ω} ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hlam measureReal_nonneg
    have h2 : 0 ≤ ∫ ω, Z 0 ω ∂μ := integral_nonneg fun ω => hnn 0 ω
    linarith
  · have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
      (f := stoppedValue Z (hitTime Z lam n)) (Eventually.of_forall fun ω => by
        simp only [Pi.zero_apply, stoppedValue]; exact hnn _ ω)
      (integrable_stoppedValue hZ lam n) lam
    have hsub := excursion_subset (Z := Z) lam n
    have hmono : μ.real {ω | ∃ t ≤ n, lam ≤ Z t ω} ≤ μ.real {ω | lam ≤ stoppedValue Z (hitTime Z lam n) ω} :=
      measureReal_mono hsub
    calc lam * μ.real {ω | ∃ t ≤ n, lam ≤ Z t ω}
        ≤ lam * μ.real {ω | lam ≤ stoppedValue Z (hitTime Z lam n) ω} :=
          mul_le_mul_of_nonneg_left hmono hlam.le
      _ ≤ ∫ ω, stoppedValue Z (hitTime Z lam n) ω ∂μ := hmarkov
      _ ≤ ∫ ω, Z 0 ω ∂μ := integral_stoppedValue_le hZ lam n

/-- Ville in the `ENNReal` form of the mandate: `ofReal λ · μ {…} ≤ ofReal (∫ Z_0)`.
Source: mandate T7(b)(ii). Kind: L. Fidelity: exact -/
theorem ville_ennreal {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (hnn : ∀ t ω, 0 ≤ Z t ω) {lam : ℝ}
    (hlam : 0 < lam) (n : ℕ) :
    ENNReal.ofReal lam * μ {ω | ∃ t ≤ n, lam ≤ Z t ω} ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂μ) := by
  have h := ville hZ hnn lam n
  have hfin : μ {ω | ∃ t ≤ n, lam ≤ Z t ω} ≠ ⊤ := measure_ne_top _ _
  calc ENNReal.ofReal lam * μ {ω | ∃ t ≤ n, lam ≤ Z t ω}
      = ENNReal.ofReal (lam * μ.real {ω | ∃ t ≤ n, lam ≤ Z t ω}) := by
        rw [ENNReal.ofReal_mul hlam.le, measureReal_def, ENNReal.ofReal_toReal hfin]
    _ ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂μ) := ENNReal.ofReal_le_ofReal h

/-- **The source's ratio form**: `P*(∃ t ≤ T, Z_t ≥ λ) ≤ Ψ₀/λ` for `λ > 0` when `Z_0 ≡ Ψ₀`.
Source: [[corr-wf14-inventory]] 078 / invariant-final.md Statement 8(b)
Kind: L
Fidelity: exact -/
theorem ville_ratio {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (hnn : ∀ t ω, 0 ≤ Z t ω) (psi0 : ℝ)
    (h0 : ∀ ω, Z 0 ω = psi0) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    μ.real {ω | ∃ t ≤ n, lam ≤ Z t ω} ≤ psi0 / lam := by
  rw [le_div_iff₀ hlam, mul_comm]
  have h := ville hZ hnn lam n
  have e : (fun ω => Z 0 ω) = fun _ => psi0 := funext h0
  rw [e] at h
  simpa [integral_const] using h

/-! ### The surviving neighbour of Statement 11(c), and Lévy -/

/-- **A nonnegative supermartingale converges a.s. to *some* limit** (not to `0`): the surviving
neighbour of the develop's 11(c), from `Submartingale.ae_tendsto_limitProcess` on `−Z` with the `L¹`
bound `∫ |Z_n| = ∫ Z_n ≤ ∫ Z_0`.
Source: [[corr-wf14-inventory]] 081, 2-019 / invariant-final.md Statement 11(b) ("a nonnegative supermartingale converges a.s. to some `d_∞ ≥ 0`")
Kind: C (Mathlib's martingale convergence theorem)
Fidelity: exact
Hyps: (a) only -/
theorem ae_tendsto_of_nonneg {Z : ℕ → Ω → ℝ} (hZ : Supermartingale Z ℱ μ) (hnn : ∀ t ω, 0 ≤ Z t ω) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n => Z n ω) atTop (𝓝 c) := by
  have hsub : Submartingale (-Z) ℱ μ := hZ.neg
  have hbdd : ∀ n, eLpNorm ((-Z) n) 1 μ ≤ ENNReal.ofReal (∫ ω, Z 0 ω ∂μ) := by
    intro n
    have h1 : eLpNorm ((-Z) n) 1 μ = ENNReal.ofReal (∫ ω, Z n ω ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      have e : (fun x => ‖(-Z) n x‖ₑ) = fun x => ‖Z n x‖ₑ := by funext x; simp
      rw [e, ← ofReal_integral_norm_eq_lintegral_enorm (hZ.integrable n)]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [Real.norm_eq_abs, abs_of_nonneg (hnn n ω)]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (integral_antitone hZ n)
  have hlim := hsub.ae_tendsto_limitProcess (R := (ENNReal.ofReal (∫ ω, Z 0 ω ∂μ)).toNNReal)
    (by
      intro n
      rw [ENNReal.coe_toNNReal (ENNReal.ofReal_ne_top)]
      exact hbdd n)
  filter_upwards [hlim] with ω hω
  refine ⟨-ℱ.limitProcess (-Z) μ ω, ?_⟩
  have := hω.neg
  simpa using this

/-- **Statement 7(c′), Lévy's conditional Borel–Cantelli** (cited from Mathlib, grade (a)): for an
adapted sequence of events `s`, `{∑_k P(s_{k+1} ∣ ℱ_k) = ∞} =ᵐ limsup s`.
Source: [[corr-wf14-inventory]] 077, 2-024 / invariant-final.md Statement 7(c) ("[reconstructed, from memory]")
Kind: C (Mathlib `ae_mem_limsup_atTop_iff`)
Fidelity: exact (the source's statement is Mathlib's) -/
theorem levy_borel_cantelli {s : ℕ → Set Ω} (hs : ∀ n, MeasurableSet[ℱ n] (s n)) :
    ∀ᵐ ω ∂μ, (ω ∈ limsup s atTop ↔
      Tendsto (fun n => ∑ k ∈ range n, (μ[(s (k + 1)).indicator (1 : Ω → ℝ)|ℱ k]) ω) atTop atTop) :=
  ae_mem_limsup_atTop_iff μ hs

end Martingale

end Cleanroom.Corrigibility.CorrTrajectory
