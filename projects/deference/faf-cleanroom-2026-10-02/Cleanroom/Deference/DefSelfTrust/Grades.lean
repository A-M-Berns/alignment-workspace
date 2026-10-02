import Cleanroom.Deference.DefSelfTrust.SelfInstances
import Cleanroom.Deference.DefSelfTrust.Ramp
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# `def-self-trust` — target 8: the margin-free grades in the self-case

root-deference-2-007 ([[li-deference]] lines 233–247, 268): the draft claims the two stronger
grades — the per-day pointwise gated law `q_n ≳ₙ 0` and the bounded margin-free violation sum
`Σ v_n < ∞` — "will turn out to be infeasible", leaving only the bounded `ε`-violation sum. The
note is explicit about its reading: its display at line 233 defines
`a_n := E^A_n(⌜E^H_{f(n)}(X)⌝)` — the AI's expectation of the humans' future expectation, the
**cross-process** case (the inventory's reading (α)) — and its commentary at line 272 says the
pointwise law "is not forceable (it needs the per-day tower)". The inventory's "(α)/(β)
ill-posed" flag, copied into the mandate and into round 1's finding F5, was wrong: there is no
open reading in the note (round-1 fidelity audit B1; F5 rewritten as a contrast finding). This
file treats the **self-case specialization** (β), `a_n := E^H_n(⌜E^H_{f(n)}(X_n)⌝)`, where the
per-day tower the note says is needed is `cee` — free:

* **8a** (`selfCase_pointwise_gated_law`): in the self-case the pointwise law
  `q_n := g_n (e_n − t) ≳ₙ 0` is **free** — `cee` gives `a_n ≈ₙ e_n`, the ramp is
  `1/δ`-Lipschitz, and no-false-positives gives `ctsInd δ e t · (e − t) ≥ 0`. This *confirms*
  the note's own diagnosis at the one instance where the tower is free; the note's claim for
  the cross-process case is untouched here (`tt-ladder`/`li-quote-lane`; finding F5);
* **8b** (`selfV_le_sq`, `summable_selfV_of_summable_sq`): the margin-free violation
  `v_n := g_n · Ind_δ(e_n < t)` is bounded by `((a_n − e_n)/(2δ))²` (AM–GM on
  `(a − t)⁺(t − e)⁺`), so a square-summable `cee` gap forces `Σ v_n < ∞`; in (β) the margin-free
  sum is governed by the square of the `cee` gap on gated days — a rate no FAF theorem controls.
  Whether `Σ v_n = ∞` can happen for the paper inductor is stated **OPEN**
  (`selfV_divergent_open`), with this diagnosis; no witness is fabricated from a point history.

The note's `X` is fixed while the corpus's LUVs vary with `n`; everything is stated for a
sequence `X_n` (the fixed case is `X_n := X₀`). `w_n` at margin `ε = 0` is `v_n`.
-/

namespace Cleanroom.Deference.DefSelfTrust

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice
open Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## The objects, on real sequences -/

/-- The gate `g_n := Ind_δ(a_n > t)` of a real sequence `a`.
Source: root-deference-2-007 (`li-deference.md:233–246`, reading (β))
Kind: D
Fidelity: exact -/
def selfGate (δ t : ℚ) (a : ℕ → ℝ) (n : ℕ) : ℝ := ctsInd δ (a n) (t : ℝ)

/-- The pointwise gated law's summand `q_n := g_n (e_n − t)`.
Source: root-deference-2-007
Kind: D
Fidelity: exact -/
def selfQ (δ t : ℚ) (a e : ℕ → ℝ) (n : ℕ) : ℝ := selfGate δ t a n * (e n - (t : ℝ))

/-- The margin-free violation `v_n := g_n · Ind_δ(e_n < t)` (`w_n` at margin `ε = 0`).
Source: root-deference-2-007
Kind: D
Fidelity: exact -/
def selfV (δ t : ℚ) (a e : ℕ → ℝ) (n : ℕ) : ℝ := selfGate δ t a n * ctsInd δ (t : ℝ) (e n)

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- The self-reading's `a_n := E_n(⌜E_{f(n)}(X_n)⌝)` at FAF's deferred-expectation quote.
Source: root-deference-2-007 (reading (β))
Kind: D
Fidelity: exact -/
def selfA (f : DeferralFunction) (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) (n : ℕ) :
    ℝ :=
  ((paperDeferredExpectationQuoteCode T f X hX).luv n).expect (liaHistory (paperDP T)) n

/-- `e_n := E_n(X_n)`.
Source: root-deference-2-007
Kind: D
Fidelity: exact -/
def selfE (X : ℕ → LUV) (n : ℕ) : ℝ := (X n).expect (liaHistory (paperDP T)) n

/-! ## 8a — the pointwise gated law is free in the self-reading -/

/-- **8a: in the self-case specialization the pointwise gated law is free**:
`q_n = Ind_δ(a_n > t)(e_n − t) ≳ₙ 0` for the self-expert over the paper's inductor, every e.c.
world-valued `X`, `δ > 0` and every `t`. Proof: `cee` (`a ≈ₙ e`), the ramp is `1/δ`-Lipschitz
(`ctsInd_lipschitz`), and `Ind_δ(e > t)(e − t) ≥ 0` pointwise (`sub_mul_ctsInd_nonneg`), with
`|e − t| ≤ 1 + |t|`. The note's "infeasible" is a cross-process claim
(`a_n := E^A_n(…)`, `li-deference.md:233`) whose own commentary (`:272`) says the pointwise law
needs the per-day tower; in the self-case that tower is `cee` and free, so this theorem
confirms the note's diagnosis at the one instance where the tower is free — it does not expose
an imprecision in the note (finding F5, rewritten in repair round 1).
Source: root-deference-2-007 (`li-deference.md:233, 272`); mandate target 8a
Kind: C
Fidelity: exact (real sequences over FAF's quotes)
Hyps: (a) -/
theorem selfCase_pointwise_gated_law (f : DeferralFunction) (X : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP T) X) {δ : ℚ} (hδ : 0 < δ)
    (t : ℚ) :
    (fun n => selfQ δ t (selfA T f X hX) (selfE T X) n) ≳ₙ (fun _ => (0 : ℝ)) := by
  have hcee : (fun n => selfE T X n) ≈ₙ (fun n => selfA T f X hX n) :=
    lic_expected_future_expectations_closed T f X hX hval
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hbound : ∀ n, |selfE T X n - (t : ℝ)| ≤ 1 + |(t : ℝ)| := fun n => by
    have h := LUV.expect_mem_Icc (liaHistory (paperDP T)) n (X n)
      (fun s => IsLogicalInductor.price_mem_Icc (P := liaHistory (paperDP T)) (DP := paperDP T)
        n s)
    calc |selfE T X n - (t : ℝ)| ≤ |selfE T X n| + |(t : ℝ)| := abs_sub _ _
      _ ≤ 1 + |(t : ℝ)| := by
          have : |selfE T X n| ≤ 1 := by
            rw [abs_le]; unfold selfE; constructor <;> linarith [h.1, h.2]
          linarith
  intro ε hε
  have hgap : Tendsto (fun n => |selfE T X n - selfA T f X hX n|) atTop (𝓝 0) := by
    have h : Tendsto (fun n => selfE T X n - selfA T f X hX n) atTop (𝓝 0) := hcee
    simpa using h.abs
  have hpos : (0 : ℝ) < ε * δ / (1 + |(t : ℝ)|) := by positivity
  filter_upwards [hgap.eventually (gt_mem_nhds hpos)] with n hn
  set a := selfA T f X hX n
  set e := selfE T X n
  have hlip : |ctsInd δ a (t : ℝ) - ctsInd δ e (t : ℝ)| ≤ |a - e| / (δ : ℝ) :=
    (ctsInd_lipschitz hδ a e (t : ℝ)).trans (min_le_right _ _)
  have hnf := sub_mul_ctsInd_nonneg hδ e (t : ℝ)
  have hae : |a - e| < ε * δ / (1 + |(t : ℝ)|) := by rwa [abs_sub_comm] at hn
  -- `q = ctsInd δ a t (e − t) = ctsInd δ e t (e − t) + (ctsInd δ a t − ctsInd δ e t)(e − t)`
  have hprod : |(ctsInd δ a (t : ℝ) - ctsInd δ e (t : ℝ)) * (e - (t : ℝ))| ≤
      (|a - e| / (δ : ℝ)) * (1 + |(t : ℝ)|) := by
    rw [abs_mul]
    exact mul_le_mul hlip (hbound n) (abs_nonneg _) (div_nonneg (abs_nonneg _) hδR.le)
  have hsmall : (|a - e| / (δ : ℝ)) * (1 + |(t : ℝ)|) < ε := by
    have h1 : (0 : ℝ) < 1 + |(t : ℝ)| := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hδR]
    calc |a - e| * (1 + |(t : ℝ)|) < ε * δ / (1 + |(t : ℝ)|) * (1 + |(t : ℝ)|) :=
          mul_lt_mul_of_pos_right hae h1
      _ = ε * δ := by field_simp
  show (0 : ℝ) ≤ selfQ δ t (selfA T f X hX) (selfE T X) n + ε
  unfold selfQ selfGate
  have hkey : ctsInd δ a (t : ℝ) * (e - (t : ℝ)) =
      (e - (t : ℝ)) * ctsInd δ e (t : ℝ) +
        (ctsInd δ a (t : ℝ) - ctsInd δ e (t : ℝ)) * (e - (t : ℝ)) := by ring
  rw [hkey]
  linarith [(abs_le.1 hprod).1]

/-! ## 8b — the margin-free violation is governed by the square of the `cee` gap -/

/-- **8b, the bound:** `v_n ≤ ((a_n − e_n)/(2δ))²` whenever both ramps are at the same threshold
(AM–GM on `(a − t)⁺ (t − e)⁺`).
Source: root-deference-2-007; mandate target 8b
Kind: P
Fidelity: exact (real sequences)
Hyps: (a) none -/
theorem selfV_le_sq {δ : ℚ} (hδ : 0 < δ) (t : ℚ) (a e : ℕ → ℝ) (n : ℕ) :
    selfV δ t a e n ≤ ((a n - e n) / (2 * (δ : ℝ))) ^ 2 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold selfV selfGate
  rcases le_or_gt (a n) (t : ℝ) with hat | hat
  · rw [(ctsInd_eq_zero_iff hδ _ _).2 hat, zero_mul]
    positivity
  rcases le_or_gt (t : ℝ) (e n) with hte | hte
  · rw [(ctsInd_eq_zero_iff hδ _ _).2 hte, mul_zero]
    positivity
  -- `a > t > e`: both ramps are bounded by their linear parts
  have h1 : ctsInd δ (a n) (t : ℝ) ≤ (a n - (t : ℝ)) / (δ : ℝ) := by
    unfold ctsInd
    calc min 1 (max 0 ((a n - (t : ℝ)) / (δ : ℝ))) ≤ max 0 ((a n - (t : ℝ)) / (δ : ℝ)) :=
          min_le_right _ _
      _ = (a n - (t : ℝ)) / (δ : ℝ) := max_eq_right (div_nonneg (by linarith) hδR.le)
  have h2 : ctsInd δ (t : ℝ) (e n) ≤ ((t : ℝ) - e n) / (δ : ℝ) := by
    unfold ctsInd
    calc min 1 (max 0 (((t : ℝ) - e n) / (δ : ℝ))) ≤ max 0 (((t : ℝ) - e n) / (δ : ℝ)) :=
          min_le_right _ _
      _ = ((t : ℝ) - e n) / (δ : ℝ) := max_eq_right (div_nonneg (by linarith) hδR.le)
  have hprod : ctsInd δ (a n) (t : ℝ) * ctsInd δ (t : ℝ) (e n) ≤
      ((a n - (t : ℝ)) / (δ : ℝ)) * (((t : ℝ) - e n) / (δ : ℝ)) :=
    mul_le_mul h1 h2 (ctsInd_nonneg _ _ _) (div_nonneg (by linarith) hδR.le)
  refine hprod.trans ?_
  -- AM–GM: `(a − t)(t − e) ≤ ((a − e)/2)²`
  have hamgm : (a n - (t : ℝ)) * ((t : ℝ) - e n) ≤ ((a n - e n) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a n + e n - 2 * (t : ℝ))]
  calc ((a n - (t : ℝ)) / (δ : ℝ)) * (((t : ℝ) - e n) / (δ : ℝ))
      = (a n - (t : ℝ)) * ((t : ℝ) - e n) / (δ : ℝ) ^ 2 := by ring
    _ ≤ ((a n - e n) / 2) ^ 2 / (δ : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hamgm (by positivity)
    _ = ((a n - e n) / (2 * (δ : ℝ))) ^ 2 := by ring

/-- **8b, the consequence:** a square-summable `cee` gap forces `Σ v_n < ∞`. In the
self-reading the margin-free sum is governed by the square of the `cee` gap on gated days — a
rate statement no FAF theorem controls.
Source: root-deference-2-007; mandate target 8b
Kind: P
Fidelity: exact (real sequences)
Hyps: (a) none -/
theorem summable_selfV_of_summable_sq {δ : ℚ} (hδ : 0 < δ) (t : ℚ) (a e : ℕ → ℝ)
    (h : Summable (fun n => (a n - e n) ^ 2)) : Summable (selfV δ t a e) := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hs : Summable (fun n => ((a n - e n) / (2 * (δ : ℝ))) ^ 2) := by
    have := h.mul_left (1 / (2 * (δ : ℝ)) ^ 2)
    refine this.congr (fun n => ?_)
    field_simp
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => selfV_le_sq hδ t a e n) hs
  unfold selfV selfGate
  exact mul_nonneg (ctsInd_nonneg _ _ _) (ctsInd_nonneg _ _ _)

/-- **OPEN (8b):** there is an e.c. world-valued source `X` and `(t, δ)`, `δ > 0`, with
`Σ v_n = ∞` for the paper inductor over `𝗣𝗔` at `succDeferral` — the margin-free grade is
genuinely unattainable in the self-reading. Diagnosis: by `summable_selfV_of_summable_sq` this
needs a `cee` gap `a_n − e_n` that is not square-summable on gated days, a rate statement no FAF
theorem controls (`cee` is a limit, not a rate); a witness would need a source whose deferred
expectation creeps to `t` from above while its current expectation sits below, infinitely often
with non-summable squared gaps. No witness is fabricated from a point history
(`computableMarket_point` is not an inductor).
Source: root-deference-2-007 ("the two stronger versions will turn out to be infeasible");
mandate target 8b
Kind: OPEN
Fidelity: exact
Hyps: n/a -/
theorem selfV_divergent_open :
    ∃ (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) (t δ : ℚ), 0 < δ ∧
      Valued (paperDP 𝗣𝗔) X ∧
      ¬ Summable (selfV δ t (selfA 𝗣𝗔 succDeferral X hX) (selfE 𝗣𝗔 X)) := by
  sorry

/-- 8a over `𝗣𝗔` at `succDeferral`, `(t, δ) = (1/2, 1/4)` (instance binders discharged).
Source: mandate design decision 1
Kind: L
Fidelity: n/a -/
example (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X) (hval : Valued (paperDP 𝗣𝗔) X) :
    (fun n => selfQ (1 / 4) (1 / 2) (selfA 𝗣𝗔 succDeferral X hX) (selfE 𝗣𝗔 X) n) ≳ₙ
      (fun _ => (0 : ℝ)) :=
  selfCase_pointwise_gated_law 𝗣𝗔 succDeferral X hX hval (by norm_num) (1 / 2)

end

end Cleanroom.Deference.DefSelfTrust
