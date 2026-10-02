import Cleanroom.Corrigibility.CorrPowerChannel.Evpi

/-!
# `corr-power-channel` — T6: linear expectation is mean-only over a first-order posterior, not
over the meta-belief algebra

* **(i)** `bestMix_eq_of_mixValue_eq`, `argmax_eq_of_mixValue_eq`: two posteriors (over possibly
  different hypothesis spaces) with the same mixture values on `B` have the same best value and
  the same argmax set — the linear rule reads nothing but the mean (Kind L). Witness E7
  (`e7_mean_only`): posterior A (one hypothesis, `V(y) = 3/5`) and posterior B (`V(y) = 1` w.p.
  `3/5`, `0` w.p. `2/5`) have the same mixture values `(1/2, 3/5)`, both pick `y`, and residuals
  `0` and `1/5`.
* **(iii)** The meta-belief frame (`stretch`): worlds `Ω × Fin 2` with the second coordinate the
  announced posterior (`0 = A`, `1 = B`); `metaP r` is concentrated on row `r`, so introspection is
  exact by construction; the introspective event `Σ_τ = {(ω, r) | EVPI(row r) > τ}`; the value
  hypothesis `V′(a, (ω, r)) = V_r(ω, a) − (1/5)·𝟙[a = y ∧ (ω, r) ∈ Σ_{1/10}]`. Then the *linear*
  rule over the meta-algebra picks `x` in B (`V̄′(y) = 2/5 < 1/2`) and `y` in A
  (`e7_meta_belief`): the two posteriors are told apart by the value of the introspective event.

Sources: power-wisdom-final.md S7 (l. 117), P7 (l. 177–179); power-wisdom-adversary.md S7.3
(l. 69); script E7; 2-065.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

/-! ## (i) The linear rule is mean-only -/

section MeanOnly

variable {A Ω Ω' : Type} [Fintype A] [DecidableEq A] [Fintype Ω] [Fintype Ω']

/-- **S7(i): equal mixture values give equal best values.**
Source: power-wisdom-final.md S7(i) (l. 117, "two posteriors with the same mixture choose
identically whatever their spread")
Kind: L
Fidelity: exact
Hyps: (a) agreement of the mixture values on `B` -/
theorem bestMix_eq_of_mixValue_eq (P : Distr Ω) (V : Ω → A → ℝ) (Q : Distr Ω') (W : Ω' → A → ℝ)
    {B : Finset A} (hB : B.Nonempty) (h : ∀ a ∈ B, mixValue P V a = mixValue Q W a) :
    bestMix P V B hB = bestMix Q W B hB :=
  sup'_congr hB rfl h

/-- **S7(i): equal mixture values give the same argmax set.**
Source: power-wisdom-final.md S7(i) (l. 117)
Kind: L
Fidelity: exact
Hyps: (a) agreement of the mixture values on `B` -/
theorem argmax_eq_of_mixValue_eq (P : Distr Ω) (V : Ω → A → ℝ) (Q : Distr Ω') (W : Ω' → A → ℝ)
    {B : Finset A} (hB : B.Nonempty) (h : ∀ a ∈ B, mixValue P V a = mixValue Q W a) :
    ∀ a ∈ B, (mixValue P V a = bestMix P V B hB ↔ mixValue Q W a = bestMix Q W B hB) := by
  intro a ha
  rw [h a ha, bestMix_eq_of_mixValue_eq P V Q W hB h]

end MeanOnly

/-- Posterior A: one hypothesis (`Ω = Fin 1`), values `x = 1/2`, `y = 3/5`.
Source: power-wisdom-final.md P7 (l. 179); script E7
Kind: D
Fidelity: n/a (witness) -/
def e7VA : Fin 1 → Fin 2 → ℝ := fun _ => ![1 / 2, 3 / 5]

/-- Posterior B's masses `(3/5, 2/5)`. Source: script E7. Kind: D. Fidelity: n/a -/
def e7PB : Distr (Fin 2) where
  mass := ![3 / 5, 2 / 5]
  nonneg := fun s => by fin_cases s <;> norm_num
  sum_eq_one := by simp [Fin.sum_univ_two]; norm_num

/-- Posterior B's values: `x = 1/2` under both; `y = 1` under `ω₁`, `0` under `ω₂`.
Source: script E7. Kind: D. Fidelity: n/a -/
def e7VB : Fin 2 → Fin 2 → ℝ := ![![1 / 2, 1], ![1 / 2, 0]]

/-- Expectation on `Fin 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_fin1 (μ : Distr (Fin 1)) (X : Fin 1 → ℝ) : expect μ X = X 0 := by
  have h := μ.sum_eq_one
  rw [Fin.sum_univ_one] at h
  simp [expect, Fin.sum_univ_one, h]

/-- **E7 (N+): the same mixture values, the same choice, different residuals.** Posteriors A and B
have mixture values `(1/2, 3/5)` on `{x, y}`; both pick `y` (`3/5 > 1/2`); `EVPI_A = 0`,
`EVPI_B = 1/5`. Non-degenerate: B has two hypotheses of positive weight that disagree.
Source: power-wisdom-final.md S7(i) (l. 117), P7 (l. 179); script E7
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e7_mean_only :
    (∀ a, mixValue (Distr.uniform : Distr (Fin 1)) e7VA a = mixValue e7PB e7VB a) ∧
      mixValue e7PB e7VB 0 = 1 / 2 ∧ mixValue e7PB e7VB 1 = 3 / 5 ∧
      evpi (Distr.uniform : Distr (Fin 1)) e7VA univ univ_nonempty = 0 ∧
      evpi e7PB e7VB univ univ_nonempty = 1 / 5 := by
  have hu2 : (univ : Finset (Fin 2)) = {0, 1} := by decide
  have hA : ∀ a, mixValue (Distr.uniform : Distr (Fin 1)) e7VA a = (![1 / 2, 3 / 5] : Fin 2 → ℝ) a := by
    intro a; simp [mixValue, expect_fin1, e7VA]
  have hB : ∀ a, mixValue e7PB e7VB a = (![1 / 2, 3 / 5] : Fin 2 → ℝ) a := by
    intro a; fin_cases a <;> simp [mixValue, expect_fin2, e7PB, e7VB] <;> norm_num
  refine ⟨fun a => by rw [hA, hB], by rw [hB]; simp, by rw [hB]; simp, ?_, ?_⟩
  · simp only [evpi, power, bestMix, attainable, expect_fin1, hu2, sup'_pair', hA, e7VA]
    norm_num
  · have hp : power e7PB e7VB univ univ_nonempty = 4 / 5 := by
      simp only [power, attainable, expect_fin2, hu2, sup'_pair', e7PB, e7VB]
      norm_num
    have hbm : bestMix e7PB e7VB univ univ_nonempty = 3 / 5 := by
      simp only [bestMix, hu2, sup'_pair', hB]
      norm_num
    rw [evpi, hp, hbm]
    norm_num

/-! ## (iii) The meta-belief frame -/

/-- The two first-order posteriors as rows of the meta-frame (both over `Ω = Fin 2`: A puts all
mass on `ω₁`).
Source: power-wisdom-final.md P7 (l. 179, "Meta-belief case"); power-wisdom-adversary.md S7.3 (l. 111)
Kind: D
Fidelity: n/a (witness) -/
def rowP : Fin 2 → Distr (Fin 2) :=
  ![⟨![1, 0], fun s => by fin_cases s <;> norm_num, by simp [Fin.sum_univ_two]⟩, e7PB]

/-- The row value tables: A rates `y` at `3/5` under both hypotheses; B as `e7VB`.
Source: power-wisdom-final.md P7 (l. 179). Kind: D. Fidelity: n/a -/
def rowV : Fin 2 → (Fin 2 → Fin 2 → ℝ) := ![fun _ => ![1 / 2, 3 / 5], e7VB]

/-- **The meta-posterior**: concentrated on the row of the actual posterior `r₀` — introspection is
exact by construction (the row coordinate is determined).
Source: power-wisdom-final.md D4 (l. 31, "the observation event is always 'you believe this
now'"); [[corr-power-channel-mandate]] T6(iii) ("introspection must be exact by construction")
Kind: D
Fidelity: exact -/
def metaP (r₀ : Fin 2) : Distr (Fin 2 × Fin 2) where
  mass := fun ω' => if ω'.2 = r₀ then (rowP r₀).mass ω'.1 else 0
  nonneg := fun ω' => by
    split_ifs
    · exact (rowP r₀).nonneg _
    · exact le_rfl
  sum_eq_one := by
    rw [Fintype.sum_prod_type_right]
    rw [sum_eq_single r₀]
    · simp [(rowP r₀).sum_eq_one]
    · intro r _ hr
      refine sum_eq_zero fun ω _ => ?_
      simp [hr]
    · intro h; exact absurd (mem_univ r₀) h

open Classical in
/-- **The introspective event** `Σ_τ = {(ω, r) | EVPI(row r) > τ}` on `{x, y}`.
Source: power-wisdom-final.md S7(iii) (l. 117, "`Σ_τ := EVPI_t({a, ∅}) > τ` … is an event the
agent knows"); power-wisdom-adversary.md S7.3 (l. 111)
Kind: D
Fidelity: exact -/
def sigmaEvent (τ : ℝ) : Finset (Fin 2 × Fin 2) :=
  univ.filter (fun ω' => τ < evpi (rowP ω'.2) (rowV ω'.2) univ univ_nonempty)

open Classical in
/-- **The meta-value hypothesis**: `V′((ω, r), a) = V_r(ω, a) − (1/5)·𝟙[a = y ∧ (ω, r) ∈ Σ_{1/10}]`
— acting on `y` while the residual exceeds `1/10` is worth `−1/5`; content supplied from outside
the agent's evidence.
Source: power-wisdom-final.md P7 (l. 179, "acting on `y` while `EVPI_t({y, x}) > 1/10` is worth
`−1/5`")
Kind: D
Fidelity: exact -/
def metaV : Fin 2 × Fin 2 → Fin 2 → ℝ := fun ω' a =>
  rowV ω'.2 ω'.1 a - (1 / 5) * (if a = 1 ∧ ω' ∈ sigmaEvent (1 / 10) then 1 else 0)

/-- The residuals of the two rows: `0` and `1/5`. Source: script E7. Kind: L. Fidelity: n/a -/
theorem evpi_rows :
    evpi (rowP 0) (rowV 0) univ univ_nonempty = 0 ∧ evpi (rowP 1) (rowV 1) univ univ_nonempty = 1 / 5 := by
  have hu2 : (univ : Finset (Fin 2)) = {0, 1} := by decide
  constructor
  · simp only [evpi, power, bestMix, attainable, mixValue, expect_fin2, hu2, sup'_pair', rowP, rowV]
    norm_num
  · simp only [evpi, power, bestMix, attainable, mixValue, expect_fin2, hu2, sup'_pair', rowP, rowV,
      e7PB, e7VB]
    norm_num

/-- Membership in `Σ_{1/10}` is decided by the row: `false` on row A, `true` on row B.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem mem_sigmaEvent (ω : Fin 2) :
    (ω, (0 : Fin 2)) ∉ sigmaEvent (1 / 10) ∧ (ω, (1 : Fin 2)) ∈ sigmaEvent (1 / 10) := by
  constructor
  · rw [sigmaEvent, mem_filter]
    simp only [mem_univ, true_and]
    rw [evpi_rows.1]
    norm_num
  · rw [sigmaEvent, mem_filter]
    simp only [mem_univ, true_and]
    rw [evpi_rows.2]
    norm_num

/-- Expectation under `metaP`, reduced to the row. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem expect_metaP (r₀ : Fin 2) (X : Fin 2 × Fin 2 → ℝ) :
    expect (metaP r₀) X = ∑ ω, (rowP r₀).mass ω * X (ω, r₀) := by
  unfold expect
  rw [Fintype.sum_prod_type_right, sum_eq_single r₀]
  · simp [metaP]
  · intro r _ hr
    refine sum_eq_zero fun ω _ => ?_
    simp [metaP, hr]
  · intro h; exact absurd (mem_univ r₀) h

/-- **S7(iii)/2-065(b): over the meta-belief algebra the linear rule is not mean-only.** With the
same first-order mixture values `(1/2, 3/5)` (E7), the meta-posterior concentrated on row B gives
`V̄′(y) = 3/5 − 1/5 = 2/5 < 1/2 = V̄′(x)` — the linear rule picks `x` — while on row A
`V̄′(y) = 3/5 > 1/2` and it picks `y`. The introspective event is exact by construction (the row
is the actual posterior), not a hypothesis `P′(Σ) = 1`.
Source: power-wisdom-final.md S7(iii) (l. 117), P7 (l. 179); power-wisdom-adversary.md S7.3 (l. 111)
Kind: N+
Fidelity: exact (the finite meta-frame of two announced posteriors)
Hyps: none -/
theorem e7_meta_belief :
    mixValue (metaP 1) metaV 1 = 2 / 5 ∧ mixValue (metaP 1) metaV 0 = 1 / 2 ∧
      mixValue (metaP 0) metaV 1 = 3 / 5 ∧ mixValue (metaP 0) metaV 0 = 1 / 2 := by
  have hB1 : ∀ ω : Fin 2, metaV (ω, 1) 1 = rowV 1 ω 1 - 1 / 5 := by
    intro ω
    dsimp only [metaV]
    rw [if_pos ⟨rfl, (mem_sigmaEvent ω).2⟩]
    ring
  have hB0 : ∀ ω : Fin 2, metaV (ω, 1) 0 = rowV 1 ω 0 := by
    intro ω
    dsimp only [metaV]
    rw [if_neg (fun h => absurd h.1 (by decide))]
    ring
  have hA1 : ∀ ω : Fin 2, metaV (ω, 0) 1 = rowV 0 ω 1 := by
    intro ω
    dsimp only [metaV]
    rw [if_neg (fun h => (mem_sigmaEvent ω).1 h.2)]
    ring
  have hA0 : ∀ ω : Fin 2, metaV (ω, 0) 0 = rowV 0 ω 0 := by
    intro ω
    dsimp only [metaV]
    rw [if_neg (fun h => absurd h.1 (by decide))]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mixValue, expect_metaP, hB1, Fin.sum_univ_two, rowP, rowV, e7PB, e7VB]
    norm_num
  · simp only [mixValue, expect_metaP, hB0, Fin.sum_univ_two, rowP, rowV, e7PB, e7VB]
    norm_num
  · simp only [mixValue, expect_metaP, hA1, Fin.sum_univ_two, rowP, rowV]
    norm_num
  · simp only [mixValue, expect_metaP, hA0, Fin.sum_univ_two, rowP, rowV]
    norm_num

end

end Cleanroom.Corrigibility.CorrPowerChannel
