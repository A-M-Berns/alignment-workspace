import Cleanroom.Info.InfoVoiLatents.Eig
import Cleanroom.Info.InfoVoiLatents.Coverage
import Cleanroom.Info.InfoVoiLatents.Shannon

/-!
# info-voi-latents — mediation buys calibration, redundancy buys coverage: the repaired S5 (Target 6)

* (i) **The min-entropy step** (A5.2, the step that replaces the develop file's backwards Fano):
  `one_sub_le_neg_log` (`1 − p ≤ −log p`), `neg_log_sup_le_entropy` (`−log (sup pi) ≤ H(pi)`, Shannon
  dominates min-entropy, carrier (i)), and over FAF **`expMiss_le_condEntropy`**:
  `E[1 − P(Λ | Y)] ≤ H[Λ | Y ; μ]` — the expected posterior miss of the truth, *averaged over the
  joint* (the designer's expectation, P5(ii)'s "when `y` is drawn from the true joint"), is at most
  the conditional entropy in nats. With `err_le_mul_one_sub` (`err ≤ M·(1 − P λH)` pointwise) this
  is `E_y[err_y] ≤ M · H[Λ | Y]`.
* (ii) `condEntropy_le_eig_add_noise`: `H[Λ_C | X_{≤t}] ≤ EIG(Λ) + ν` with `ν = H[Λ_C | ⟨X_k, X_{≤t}⟩]`,
  for `Λ_C = f ∘ Λ` (chain rule + conditional data processing).
* (iii) **`tv_mix_le`**: a mixture through a common kernel contracts total variation,
  `tv (K ⋆ P) (K ⋆ Q) ≤ tv P Q` — the step behind P5(i)'s first gap (with Pinsker and Jensen, which
  are `Finite.lean`'s). The assembly under H3–H4 is in `MediationAssembly.lean` (repair round 2:
  `predictive_tv_assembly`, `expected_miss_assembly`, `expected_err_assembly`).

Mandate: Target 6 (i)–(iii).
-/

namespace Cleanroom.Info.InfoVoiLatents.Mediation

open MeasureTheory ProbabilityTheory Finset Real
open Cleanroom.Info.InfoVoiLatents.Eig Cleanroom.Info.InfoVoiLatents.Coverage
open Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

/-! ### (i) The min-entropy step -/

/-- `1 − p ≤ −log p` for `0 < p`.
Source: [[generalization-adversary]] A5.2 l. 58 ("`−ln(1 − p_e) ≥ p_e`"); none: infrastructure
Kind: L
Fidelity: n/a -/
theorem one_sub_le_neg_log {p : ℝ} (hp : 0 < p) : 1 - p ≤ -Real.log p := by
  have := Real.log_le_sub_one_of_pos hp
  linarith

/-- **Shannon dominates min-entropy** on a finite carrier: for a distribution `π` with maximum `m`,
`−log m ≤ ∑ w, negMulLog (π w)` (zero coordinates contribute `0` on both sides).
Source: [[generalization-adversary]] A5.2 l. 58 ("`H(Λ | Y = y) ≥ −ln max_λ P(λ | y)`")
Kind: P
Fidelity: exact -/
theorem neg_log_sup_le_entropy {W : Type} [Fintype W] {pi : W → ℝ} (hπ : pi ∈ stdSimplex ℝ W)
    (hne : (univ : Finset W).Nonempty) :
    -Real.log (univ.sup' hne pi) ≤ ∑ w, negMulLog (pi w) := by
  have hm : 0 < univ.sup' hne pi := by
    obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup' hne pi
    rw [hw]
    by_contra h
    push Not at h
    have : ∑ w, pi w ≤ 0 := Finset.sum_nonpos fun w' _ =>
      le_trans (Finset.le_sup' pi (mem_univ w')) (hw ▸ h)
    rw [hπ.2] at this
    linarith
  calc -Real.log (univ.sup' hne pi) = ∑ w, pi w * (-Real.log (univ.sup' hne pi)) := by
        rw [← Finset.sum_mul, hπ.2, one_mul]
    _ ≤ ∑ w, negMulLog (pi w) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rcases (hπ.1 w).lt_or_eq with hw | hw
        · unfold negMulLog
          have := Real.log_le_log hw (Finset.le_sup' pi (mem_univ w))
          nlinarith
        · rw [← hw]
          simp

variable {Ω : Type*} {S T : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype S] [Fintype T] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSingletonClass S]
  [MeasurableSingletonClass T]

/-- **The expected posterior miss of the truth**, averaged over the joint law of `(Λ, Y)`:
`E[1 − P(Λ | Y)] = ∑ λ, ∑ y, P(λ, y) · (1 − P(λ, y) / P(y))` (junk-safe: a null `y` contributes `0`).
Source: [[generalization-final]] P5(ii) l. 125 ("`M(1 − π*_y)`, when `y` is drawn from the true
joint")
Kind: D
Fidelity: exact (the designer's expectation over the joint) -/
def expMiss (μ : Measure Ω) (Λ : Ω → S) (Y : Ω → T) : ℝ :=
  ∑ l, ∑ y, pm2 μ Λ Y l y * (1 - pm2 μ Λ Y l y / pm1 μ Y y)

/-- `H[Λ | Y ; μ] = ∑ λ, ∑ y, P(λ, y) · (−log (P(λ, y) / P(y)))` on a finite carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condEntropy_eq_sum_pm2 {Λ : Ω → S} {Y : Ω → T} (hΛ : Measurable Λ) (hY : Measurable Y) :
    H[Λ | Y ; μ] = ∑ l, ∑ y, pm2 μ Λ Y l y * (-Real.log (pm2 μ Λ Y l y / pm1 μ Y y)) := by
  rw [ShannonInformation.chain_rule'' μ hΛ hY, entropy_pair_eq_sum_pm2 hΛ hY, entropy_eq_sum_pm1 hY]
  have h1 : ∑ y, negMulLog (pm1 μ Y y) = ∑ l, ∑ y, pm2 μ Λ Y l y * (-Real.log (pm1 μ Y y)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, sum_pm2_x hΛ, negMulLog]
    ring
  rw [h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rcases (pm2_nonneg (μ := μ) Λ Y l y).lt_or_eq with h | h
  · have hy : 0 < pm1 μ Y y := lt_of_lt_of_le h (measureReal_mono Set.inter_subset_right)
    rw [Real.log_div h.ne' hy.ne', negMulLog]
    ring
  · rw [← h]
    simp

/-- **The min-entropy bound over FAF**: `E[1 − P(Λ | Y)] ≤ H[Λ | Y ; μ]` — the expected posterior
miss of the truth (averaged over the joint) is at most the conditional entropy in nats. Per
cell: `1 − x ≤ −log x` at `x = P(λ, y)/P(y) ∈ (0, 1]`.
Source: [[generalization-final]] S5(ii) l. 73, P5(ii) l. 125 ("by the min-entropy bound, *not*
Fano"); [[generalization-adversary]] A5.2 l. 58; items 129, 2-072
Kind: P
Fidelity: exact (in expectation over the data; the pointwise form fails, A5.4)
Hyps: (a) all -/
theorem expMiss_le_condEntropy {Λ : Ω → S} {Y : Ω → T} (hΛ : Measurable Λ) (hY : Measurable Y) :
    expMiss μ Λ Y ≤ H[Λ | Y ; μ] := by
  rw [condEntropy_eq_sum_pm2 hΛ hY]
  unfold expMiss
  refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun y _ => ?_
  rcases (pm2_nonneg (μ := μ) Λ Y l y).lt_or_eq with h | h
  · refine mul_le_mul_of_nonneg_left ?_ h.le
    have hy : 0 < pm1 μ Y y := lt_of_lt_of_le h (measureReal_mono Set.inter_subset_right)
    exact one_sub_le_neg_log (div_pos h hy)
  · rw [← h]
    simp

/-- **Pointwise, the error is at most `M` times the posterior miss of the truth**:
`|E_P[V̄ a] − V̄(a, λH)| ≤ M · (1 − P λH)` for a profile of range `M` (only the mass off the truth
can contribute).
Source: [[generalization-final]] P5(ii) l. 125 ("`err(a) ≤ ∑ π_y(prof)|…| ≤ M(1 − π*_y)`")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem err_le_mul_one_sub {Λ' α : Type} [Fintype Λ'] [DecidableEq Λ'] {P : Λ' → ℝ}
    (hP : P ∈ stdSimplex ℝ Λ') {Vbar : α → Λ' → ℝ} {lH : Λ'} {M : ℝ}
    (hM : ∀ a l l', Vbar a l - Vbar a l' ≤ M) (a : α) :
    |E P (Vbar a) - Vbar a lH| ≤ M * (1 - P lH) := by
  have hdiff : E P (Vbar a) - Vbar a lH = ∑ l, P l * (Vbar a l - Vbar a lH) := by
    unfold E
    rw [Finset.sum_congr rfl fun l _ => mul_sub (P l) (Vbar a l) (Vbar a lH),
      Finset.sum_sub_distrib, ← Finset.sum_mul, hP.2, one_mul]
  have hoff : ∑ l ∈ univ.erase lH, P l = 1 - P lH := by
    have := Finset.sum_erase_add univ P (mem_univ lH)
    rw [hP.2] at this
    linarith
  rw [hdiff]
  calc |∑ l, P l * (Vbar a l - Vbar a lH)|
      ≤ ∑ l, |P l * (Vbar a l - Vbar a lH)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l ∈ univ.erase lH, |P l * (Vbar a l - Vbar a lH)| := by
        rw [← Finset.sum_erase_add univ _ (mem_univ lH)]
        simp
    _ ≤ ∑ l ∈ univ.erase lH, P l * M := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (hP.1 l)]
        refine mul_le_mul_of_nonneg_left ?_ (hP.1 l)
        rw [abs_le]
        exact ⟨by linarith [hM a lH l], hM a l lH⟩
    _ = M * (1 - P lH) := by rw [← Finset.sum_mul, hoff, mul_comm]

/-! ### (ii) `H[Λ_C | X_{≤t}] ≤ EIG + ν` -/

/-- **`H[Λ_C | X_{≤t}] ≤ EIG(Λ) + ν`** with `ν = H[Λ_C | ⟨X_k, X_{≤t}⟩]` the irreducible judgment noise,
for `Λ_C = f ∘ Λ` a function of the concept (chain rule + conditional data processing).
Source: [[generalization-final]] S5(ii) l. 73, P5(ii) l. 125
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem condEntropy_le_eig_add_noise {U C : Type} [Fintype U] [Fintype C] [MeasurableSpace U]
    [MeasurableSpace C] [MeasurableSingletonClass U] [MeasurableSingletonClass C]
    {Λ : Ω → S} {Xk : Ω → T} {Xle : Ω → U} (hΛ : Measurable Λ) (hXk : Measurable Xk)
    (hXle : Measurable Xle) (f : S → C) :
    H[f ∘ Λ | Xle ; μ] ≤ EIG Λ Xk Xle μ + H[f ∘ Λ | (⟨Xk, Xle⟩ : Ω → T × U) ; μ] := by
  have hf : Measurable f := measurable_of_countable f
  have h1 : H[f ∘ Λ | Xle ; μ] = I[f ∘ Λ : Xk | Xle ; μ] + H[f ∘ Λ | (⟨Xk, Xle⟩ : Ω → T × U) ; μ] := by
    rw [ShannonInformation.condMutualInfo_eq' (hf.comp hΛ) hXk hXle μ]
    ring
  have h2 : I[f ∘ Λ : Xk | Xle ; μ] ≤ I[Λ : Xk | Xle ; μ] :=
    Cleanroom.Info.InfoVoiLatents.Shannon.condMutualInfo_comp_le_left hΛ hXk hXle f
  unfold EIG
  linarith

/-! ### (iii) A common kernel contracts total variation -/

/-- The mixture of a kernel `K` by a weight vector `P`: `(K ⋆ P) x = ∑ λ, P λ · K λ x`.
Source: [[generalization-final]] P5(i) l. 125 (`P_t[X_k | X_{≤t}] = ∑_λ P^H[X_k | λ] P_t[λ | X_{≤t}]`)
Kind: D
Fidelity: exact -/
def mix {Λ' X : Type} [Fintype Λ'] (K : Λ' → X → ℝ) (P : Λ' → ℝ) : X → ℝ :=
  fun x => ∑ l, P l * K l x

/-- **A common kernel contracts total variation**: `tv (K ⋆ P) (K ⋆ Q) ≤ tv P Q` for a stochastic
`K` (rows in the simplex).
Source: [[generalization-final]] P5(i) l. 125 ("the first gap is `≤ TV(P_t(λ | X_{≤t}), P^H(λ |
X_{≤t}))`")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem tv_mix_le {Λ' X : Type} [Fintype Λ'] [Fintype X] {K : Λ' → X → ℝ}
    (hK : ∀ l, K l ∈ stdSimplex ℝ X) (P Q : Λ' → ℝ) : tv (mix K P) (mix K Q) ≤ tv P Q := by
  unfold tv mix
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ x, |∑ l, P l * K l x - ∑ l, Q l * K l x|
      = ∑ x, |∑ l, (P l - Q l) * K l x| := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ ∑ x, ∑ l, |P l - Q l| * K l x := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [abs_mul, abs_of_nonneg ((hK l).1 x)]
    _ = ∑ l, |P l - Q l| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← Finset.mul_sum, (hK l).2, mul_one]

end

end Cleanroom.Info.InfoVoiLatents.Mediation
