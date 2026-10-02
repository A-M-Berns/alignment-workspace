import Cleanroom.Lit.LitDdbFacts.Prior
import Cleanroom.Lit.LitDdbFacts.Examples

/-!
# Prior-frame witnesses (Target 17(ii)/E1)

Package `lit-ddb-facts`, after audit round 2. Three prior frames on `Fin 3`:

* **`cxQ`** (audit r2 B1, copied from the adversarial probe): prior `(1/10, 3/10, 3/5)`, evidence
  `E_0 = {0}`, `E_1 = {0, 1}`, `E_2 = {1, 2}`. Factive and nested-factive, but neither nested nor
  transitive. The prior **trusts** the induced frame (checked at every `q, p` and every real
  threshold) and **does not value** it (`X = (−6, 3, 0)`, `s = 1`). So "on prior frames Trust ⟹
  Value", DDB's fn 25 paraphrase of Dorst 2020a Theorem 7.4, is false as stated, in both the
  deferrer-is-the-prior and the separate-deferrer reading (`prior_trust_value_refuted`,
  `prior_trust_value_all_refuted`).
* **`chainQ`**: uniform prior, nested evidence `{0} ⊂ {0, 1} ⊂ {0, 1, 2}`, rows `δ_0`,
  `(½, ½, 0)`, `(⅓, ⅓, ⅓)` — two of them modest, so the immodest collapse does not apply. The
  prior simply trusts the frame, hence (`PriorFrame.totalTrust_of_nested_of_simpleTrust`) totally
  trusts and values it: the N+ witness for the nested theorem. The separate deferrer
  `π = (½, 1/5, 3/10)` simply trusts the frame but does not value it, and fails Trust at
  `q = {1}`, `p = {1, 2}`, `t = ½`: on nested prior frames a separate deferrer's Simple Trust is
  not enough, so the OPEN separate-deferrer statement genuinely needs Trust.
* **`diracQ`** (audit r2 Q5, copied): `E_w = {w}` for any regular prior; nested and immodest, so
  both the nested theorem and the collapse apply, and every deferrer's Trust implies Value.
-/

namespace Cleanroom.Lit.LitDdbFacts.ExamplesPrior

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Lit.LitDdbFacts Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

set_option linter.unusedSectionVars false

/-- Mass over a subset of three worlds as a sum of three indicators.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem massFin3 (ρ : Fin 3 → ℝ) (s : Finset (Fin 3)) :
    mass ρ s = (if (0 : Fin 3) ∈ s then ρ 0 else 0) + (if (1 : Fin 3) ∈ s then ρ 1 else 0) +
      (if (2 : Fin 3) ∈ s then ρ 2 else 0) := by
  rw [mass, ← univ_inter s, ← sum_ite_mem, Fin.sum_univ_three]
  simp only [univ_inter]

/-! ## The counterexample `cxQ` (audit r2 B1): Trust without Value on a prior frame -/

/-- The prior `μ = (1/10, 3/10, 3/5)`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: D
Fidelity: n/a -/
def cxμ : Fin 3 → ℝ := ![1 / 10, 3 / 10, 3 / 5]

/-- It is regular.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cxμ_pos : ∀ w, 0 < cxμ w := by
  intro w; fin_cases w <;> norm_num [cxμ, vec3_two, fin3_mk_two]

/-- It sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cxμ_sum : ∑ w, cxμ w = 1 := by
  norm_num [Fin.sum_univ_three, cxμ, vec3_two]

/-- The evidence map `E_0 = {0}`, `E_1 = {0, 1}`, `E_2 = {1, 2}`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: D
Fidelity: n/a -/
def cxEv : Fin 3 → Finset (Fin 3) := ![{0}, {0, 1}, {1, 2}]

/-- Evidence is nonempty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cxEv_nonempty : ∀ w, (cxEv w).Nonempty := by
  intro w; fin_cases w <;> simp [cxEv]

/-- The prior frame of the counterexample.
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: D
Fidelity: n/a -/
def cxQ : PriorFrame (Fin 3) := ⟨cxμ, cxμ_pos, cxμ_sum, cxEv, cxEv_nonempty⟩

/-- Its prior is `cxμ` (definitional).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cxQ_μ : cxQ.μ = cxμ := rfl

/-- The evidence is factive and nested-factive (findings F14's constraint holds).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem cxEv_factive : (∀ w, w ∈ cxEv w) ∧ ∀ v w, cxEv v ⊆ cxEv w → v ∈ cxEv w := by
  refine ⟨by decide, by decide⟩

/-- But neither nested nor transitive: `E_1 ∩ E_2 = {1}` with neither containing the other, and
`1 ∈ E_2` while `E_1 ⊄ E_2`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem cxEv_not_nested_not_transitive :
    (¬ (cxEv 1 ⊆ cxEv 2 ∨ cxEv 2 ⊆ cxEv 1 ∨ Disjoint (cxEv 1) (cxEv 2))) ∧
      (1 : Fin 3) ∈ cxEv 2 ∧ ¬ cxEv 1 ⊆ cxEv 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- `cxQ` is not nested (so the hypothesis of `prior_value_of_trust_of_nested` is not an
artifact: dropping it makes the theorem false).
Source: none: new (repair round 2)
Kind: L
Fidelity: n/a -/
theorem cxQ_not_nested : ¬ cxQ.Nested := fun h => by
  have := h 1 2 ⟨1, by decide⟩
  exact absurd this (by decide)

/-- The induced rows: `δ_0`, `(1/4, 3/4, 0)`, `(0, 1/3, 2/3)`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem cxQ_P : cxQ.toFrame.P 0 = ![1, 0, 0] ∧ cxQ.toFrame.P 1 = ![1 / 4, 3 / 4, 0] ∧
    cxQ.toFrame.P 2 = ![0, 1 / 3, 2 / 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext v <;> fin_cases v <;>
    simp [PriorFrame.toFrame, PriorFrame.row, cxQ, cxEv, massFin3, cxμ, vec3_two, fin3_mk_two] <;>
    norm_num

/-- The bet `X = (−6, 3, 0)`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: D
Fidelity: n/a -/
def cxX : Fin 3 → ℝ := ![-6, 3, 0]

/-- **`μ` does not totally trust the frame**: at `(X, 1)` the product sum is `−3/5` (the expert's
estimate is `≥ 1` exactly at world 2, where `X = 0`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: N+
Fidelity: n/a -/
theorem cxQ_not_totalTrust : ¬ TotalTrust cxQ.μ cxQ.toFrame := by
  intro h
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hsum := h cxX 1
  rw [Fin.sum_univ_three] at hsum
  norm_num [E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, h1, h2, cxX, cxQ_μ, cxμ] at hsum

/-- **`μ` does not value the frame** (Theorem 2.2).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: N+
Fidelity: n/a -/
theorem cxQ_not_value : ¬ Value cxQ.μ cxQ.toFrame := fun h =>
  cxQ_not_totalTrust ((value_iff_totalTrust cxQ.μ_mem cxQ.toFrame).1 h)

set_option maxHeartbeats 1000000 in
/-- Trust on the membership pattern `TTT` of `p` (see `cxQ_trust`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem trustBody_TTT {q p : Finset (Fin 3)} {t : ℝ}
    (h0p : (0 : Fin 3) ∈ p) (h1p : (1 : Fin 3) ∈ p) (h2p : (2 : Fin 3) ∈ p)
    (hpos : 0 < mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t)) :
    t * mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t) ≤
      mass cxQ.μ (q ∩ (p ∩ cxQ.toFrame.condProbEvent q p t)) := by
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hE : ∀ w, w ∈ cxQ.toFrame.condProbEvent q p t ↔
      0 < mass (cxQ.toFrame.P w) p ∧
        t * mass (cxQ.toFrame.P w) p ≤ mass (cxQ.toFrame.P w) (q ∩ p) := by
    intro w; simp [Frame.condProbEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, cxQ_μ, cxμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0p, h1p, h2p, h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true,
      and_false, add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false]
      at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

set_option maxHeartbeats 1000000 in
/-- Trust on the membership pattern `TTF` of `p` (see `cxQ_trust`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem trustBody_TTF {q p : Finset (Fin 3)} {t : ℝ}
    (h0p : (0 : Fin 3) ∈ p) (h1p : (1 : Fin 3) ∈ p) (h2p : (2 : Fin 3) ∉ p)
    (hpos : 0 < mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t)) :
    t * mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t) ≤
      mass cxQ.μ (q ∩ (p ∩ cxQ.toFrame.condProbEvent q p t)) := by
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hE : ∀ w, w ∈ cxQ.toFrame.condProbEvent q p t ↔
      0 < mass (cxQ.toFrame.P w) p ∧
        t * mass (cxQ.toFrame.P w) p ≤ mass (cxQ.toFrame.P w) (q ∩ p) := by
    intro w; simp [Frame.condProbEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, cxQ_μ, cxμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0p, h1p, h2p, h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true,
      and_false, add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false]
      at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

set_option maxHeartbeats 1000000 in
/-- Trust on the membership pattern `TFT` of `p` (see `cxQ_trust`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem trustBody_TFT {q p : Finset (Fin 3)} {t : ℝ}
    (h0p : (0 : Fin 3) ∈ p) (h1p : (1 : Fin 3) ∉ p) (h2p : (2 : Fin 3) ∈ p)
    (hpos : 0 < mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t)) :
    t * mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t) ≤
      mass cxQ.μ (q ∩ (p ∩ cxQ.toFrame.condProbEvent q p t)) := by
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hE : ∀ w, w ∈ cxQ.toFrame.condProbEvent q p t ↔
      0 < mass (cxQ.toFrame.P w) p ∧
        t * mass (cxQ.toFrame.P w) p ≤ mass (cxQ.toFrame.P w) (q ∩ p) := by
    intro w; simp [Frame.condProbEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, cxQ_μ, cxμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0p, h1p, h2p, h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true,
      and_false, add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false]
      at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

set_option maxHeartbeats 1000000 in
/-- Trust on the membership pattern `TFF` of `p` (see `cxQ_trust`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem trustBody_TFF {q p : Finset (Fin 3)} {t : ℝ}
    (h0p : (0 : Fin 3) ∈ p) (h1p : (1 : Fin 3) ∉ p) (h2p : (2 : Fin 3) ∉ p)
    (hpos : 0 < mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t)) :
    t * mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t) ≤
      mass cxQ.μ (q ∩ (p ∩ cxQ.toFrame.condProbEvent q p t)) := by
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hE : ∀ w, w ∈ cxQ.toFrame.condProbEvent q p t ↔
      0 < mass (cxQ.toFrame.P w) p ∧
        t * mass (cxQ.toFrame.P w) p ≤ mass (cxQ.toFrame.P w) (q ∩ p) := by
    intro w; simp [Frame.condProbEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, cxQ_μ, cxμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0p, h1p, h2p, h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true,
      and_false, add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false]
      at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

set_option maxHeartbeats 1000000 in
/-- Trust on the membership pattern `FTT` of `p` (see `cxQ_trust`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem trustBody_FTT {q p : Finset (Fin 3)} {t : ℝ}
    (h0p : (0 : Fin 3) ∉ p) (h1p : (1 : Fin 3) ∈ p) (h2p : (2 : Fin 3) ∈ p)
    (hpos : 0 < mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t)) :
    t * mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t) ≤
      mass cxQ.μ (q ∩ (p ∩ cxQ.toFrame.condProbEvent q p t)) := by
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hE : ∀ w, w ∈ cxQ.toFrame.condProbEvent q p t ↔
      0 < mass (cxQ.toFrame.P w) p ∧
        t * mass (cxQ.toFrame.P w) p ≤ mass (cxQ.toFrame.P w) (q ∩ p) := by
    intro w; simp [Frame.condProbEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, cxQ_μ, cxμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0p, h1p, h2p, h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true,
      and_false, add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false]
      at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

set_option maxHeartbeats 1000000 in
/-- Trust on the membership pattern `FTF` of `p` (see `cxQ_trust`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem trustBody_FTF {q p : Finset (Fin 3)} {t : ℝ}
    (h0p : (0 : Fin 3) ∉ p) (h1p : (1 : Fin 3) ∈ p) (h2p : (2 : Fin 3) ∉ p)
    (hpos : 0 < mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t)) :
    t * mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t) ≤
      mass cxQ.μ (q ∩ (p ∩ cxQ.toFrame.condProbEvent q p t)) := by
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hE : ∀ w, w ∈ cxQ.toFrame.condProbEvent q p t ↔
      0 < mass (cxQ.toFrame.P w) p ∧
        t * mass (cxQ.toFrame.P w) p ≤ mass (cxQ.toFrame.P w) (q ∩ p) := by
    intro w; simp [Frame.condProbEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, cxQ_μ, cxμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0p, h1p, h2p, h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true,
      and_false, add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false]
      at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

set_option maxHeartbeats 1000000 in
/-- Trust on the membership pattern `FFT` of `p` (see `cxQ_trust`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem trustBody_FFT {q p : Finset (Fin 3)} {t : ℝ}
    (h0p : (0 : Fin 3) ∉ p) (h1p : (1 : Fin 3) ∉ p) (h2p : (2 : Fin 3) ∈ p)
    (hpos : 0 < mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t)) :
    t * mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t) ≤
      mass cxQ.μ (q ∩ (p ∩ cxQ.toFrame.condProbEvent q p t)) := by
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hE : ∀ w, w ∈ cxQ.toFrame.condProbEvent q p t ↔
      0 < mass (cxQ.toFrame.P w) p ∧
        t * mass (cxQ.toFrame.P w) p ≤ mass (cxQ.toFrame.P w) (q ∩ p) := by
    intro w; simp [Frame.condProbEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, cxQ_μ, cxμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0p, h1p, h2p, h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true,
      and_false, add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false]
      at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

set_option maxHeartbeats 1000000 in
/-- Trust on the membership pattern `FFF` of `p` (see `cxQ_trust`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: L
Fidelity: n/a -/
theorem trustBody_FFF {q p : Finset (Fin 3)} {t : ℝ}
    (h0p : (0 : Fin 3) ∉ p) (h1p : (1 : Fin 3) ∉ p) (h2p : (2 : Fin 3) ∉ p)
    (hpos : 0 < mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t)) :
    t * mass cxQ.μ (p ∩ cxQ.toFrame.condProbEvent q p t) ≤
      mass cxQ.μ (q ∩ (p ∩ cxQ.toFrame.condProbEvent q p t)) := by
  obtain ⟨h0, h1, h2⟩ := cxQ_P
  have hE : ∀ w, w ∈ cxQ.toFrame.condProbEvent q p t ↔
      0 < mass (cxQ.toFrame.P w) p ∧
        t * mass (cxQ.toFrame.P w) p ≤ mass (cxQ.toFrame.P w) (q ∩ p) := by
    intro w; simp [Frame.condProbEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, cxQ_μ, cxμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0p, h1p, h2p, h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true,
      and_false, add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false]
      at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

/-- **`μ` trusts the frame**: for every `q, p` and every real `t`, the product-form Trust
inequality holds. Brute force in eight pieces (one per membership pattern of the three worlds in
`p`, `trustBody_*`): the memberships in `q` are split, the masses expand into indicator sums, and
the three threshold conditions defining `[P(q | p) ≥ t]` are split; every leaf is linear in `t`.
Two instances are tight: `μ(0 | {0,1}) = 1/4 = P_1(0)` and `μ(1 | {1,2}) = 1/3 = P_2(1)`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1
Kind: N+
Fidelity: n/a -/
theorem cxQ_trust : Trust cxQ.μ cxQ.toFrame := by
  intro q p t hpos
  by_cases h0p : (0 : Fin 3) ∈ p <;> by_cases h1p : (1 : Fin 3) ∈ p <;>
    by_cases h2p : (2 : Fin 3) ∈ p <;>
    first
      | exact trustBody_TTT h0p h1p h2p hpos
      | exact trustBody_TTF h0p h1p h2p hpos
      | exact trustBody_TFT h0p h1p h2p hpos
      | exact trustBody_TFF h0p h1p h2p hpos
      | exact trustBody_FTT h0p h1p h2p hpos
      | exact trustBody_FTF h0p h1p h2p hpos
      | exact trustBody_FFT h0p h1p h2p hpos
      | exact trustBody_FFF h0p h1p h2p hpos

/-- **"On prior frames Trust ⟹ Value" (deferrer-is-the-prior reading) is false as stated**: its
instance on `Fin 3` fails at `cxQ`. This is the statement the package carried as
`prior_trust_value_open` until audit round 2.
Source: [[Deference Done Better]] §2 l. 157, fn 25 (the paraphrase of Dorst 2020a Theorem 7.4);
findings F15
Kind: N+
Fidelity: n/a (refutation of the unrestricted paraphrase)
Hyps: (a) none -/
theorem prior_trust_value_refuted :
    ¬ ∀ Q : PriorFrame (Fin 3), Trust Q.μ Q.toFrame → Value Q.μ Q.toFrame := fun h =>
  cxQ_not_value (h cxQ cxQ_trust)

/-- **The separate-deferrer reading is false as stated too** (the prior itself is a deferrer).
This is the statement the package carried as `prior_trust_value_all_open` until audit round 2.
Source: [[Deference Done Better]] §2 l. 157, fn 25; findings F15
Kind: N+
Fidelity: n/a (refutation of the unrestricted paraphrase)
Hyps: (a) none -/
theorem prior_trust_value_all_refuted :
    ¬ ∀ (Q : PriorFrame (Fin 3)) (π : Fin 3 → ℝ), π ∈ stdSimplex ℝ (Fin 3) →
      Trust π Q.toFrame → Value π Q.toFrame := fun h =>
  cxQ_not_value (h cxQ cxQ.μ cxQ.μ_mem cxQ_trust)

/-- Collected: a factive, nested-factive, non-nested prior frame whose prior trusts but does not
value (nor totally trust) the induced frame.
Source: [[lit-ddb-facts-audit-r2-adversarial]] B1; findings F15
Kind: N+
Fidelity: n/a -/
theorem cxQ_summary :
    (∀ w, w ∈ cxQ.Ev w) ∧ ¬ cxQ.Nested ∧ Trust cxQ.μ cxQ.toFrame ∧ ¬ Value cxQ.μ cxQ.toFrame ∧
      ¬ TotalTrust cxQ.μ cxQ.toFrame :=
  ⟨cxEv_factive.1, cxQ_not_nested, cxQ_trust, cxQ_not_value, cxQ_not_totalTrust⟩

/-! ## `chainQ`: a nested prior frame with modest rows -/

/-- The uniform prior on three worlds.
Source: none: new (repair round 2)
Kind: D
Fidelity: n/a -/
def chainμ : Fin 3 → ℝ := ![1 / 3, 1 / 3, 1 / 3]

/-- It is regular.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chainμ_pos : ∀ w, 0 < chainμ w := by
  intro w; fin_cases w <;> norm_num [chainμ, vec3_two, fin3_mk_two]

/-- It sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chainμ_sum : ∑ w, chainμ w = 1 := by
  norm_num [Fin.sum_univ_three, chainμ, vec3_two]

/-- The chain evidence `E_0 = {0} ⊂ E_1 = {0, 1} ⊂ E_2 = {0, 1, 2}`.
Source: none: new (repair round 2)
Kind: D
Fidelity: n/a -/
def chainEv : Fin 3 → Finset (Fin 3) := ![{0}, {0, 1}, {0, 1, 2}]

/-- Evidence is nonempty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chainEv_nonempty : ∀ w, (chainEv w).Nonempty := by
  intro w; fin_cases w <;> simp [chainEv]

/-- The nested prior frame with chain evidence and uniform prior.
Source: none: new (repair round 2)
Kind: D
Fidelity: n/a -/
def chainQ : PriorFrame (Fin 3) := ⟨chainμ, chainμ_pos, chainμ_sum, chainEv, chainEv_nonempty⟩

/-- Its prior is `chainμ` (definitional).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chainQ_μ : chainQ.μ = chainμ := rfl

/-- `chainQ` is nested.
Source: none: new (repair round 2)
Kind: L
Fidelity: n/a -/
theorem chainQ_nested : chainQ.Nested := by
  intro v w _
  fin_cases v <;> fin_cases w <;> decide

/-- The induced rows: `δ_0`, `(½, ½, 0)`, `(⅓, ⅓, ⅓)`.
Source: none: new (repair round 2)
Kind: L
Fidelity: n/a -/
theorem chainQ_P : chainQ.toFrame.P 0 = ![1, 0, 0] ∧ chainQ.toFrame.P 1 = ![1 / 2, 1 / 2, 0] ∧
    chainQ.toFrame.P 2 = ![1 / 3, 1 / 3, 1 / 3] := by
  refine ⟨?_, ?_, ?_⟩ <;> funext v <;> fin_cases v <;>
    simp [PriorFrame.toFrame, PriorFrame.row, chainQ, chainEv, massFin3, chainμ, vec3_two,
      fin3_mk_two] <;>
    norm_num

/-- Rows 0 and 1 differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chainQ_ne01 : chainQ.toFrame.P 0 ≠ chainQ.toFrame.P 1 := by
  intro h
  have := congrFun h 0
  rw [chainQ_P.1, chainQ_P.2.1] at this
  norm_num at this

/-- Rows 2 and 1 differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chainQ_ne21 : chainQ.toFrame.P 2 ≠ chainQ.toFrame.P 1 := by
  intro h
  have := congrFun h 2
  rw [chainQ_P.2.2, chainQ_P.2.1] at this
  norm_num [vec3_two] at this

/-- The cell of row 1 is `{1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chainQ_cell1 : chainQ.toFrame.cell (chainQ.toFrame.P 1) = {1} := by
  ext w
  rw [Frame.mem_cell, mem_singleton]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  by_contra hne
  fin_cases w
  · exact chainQ_ne01 h
  · exact hne rfl
  · exact chainQ_ne21 h

/-- **Row 1 of `chainQ` is modest** (`P_1(P = P_1) = ½`), so the immodest collapse
(`tfae_immodestFrame`) does not cover this frame; the nested theorem is what makes the prior
value it.
Source: none: new (repair round 2)
Kind: N+
Fidelity: n/a -/
theorem chainQ_modestAt1 : chainQ.toFrame.ModestAt 1 := by
  show chainQ.toFrame.selfMass (chainQ.toFrame.P 1) < 1
  rw [Frame.selfMass, chainQ_cell1, mass_singleton, chainQ_P.2.1]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **The prior simply trusts `chainQ`**: brute force over the memberships in `q` and the three
threshold comparisons.
Source: none: new (repair round 2)
Kind: N+
Fidelity: n/a -/
theorem chainQ_simpleTrust : SimpleTrust chainQ.μ chainQ.toFrame := by
  intro q t hpos
  obtain ⟨h0, h1, h2⟩ := chainQ_P
  have hE : ∀ w, w ∈ chainQ.toFrame.probEvent q t ↔ t ≤ mass (chainQ.toFrame.P w) q := by
    intro w; simp [Frame.probEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, chainQ_μ, chainμ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true, and_false,
      add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false] at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

/-- **N+ witness for the nested theorem**: `chainQ` is nested, its prior simply trusts it, hence
(`PriorFrame.totalTrust_of_nested_of_simpleTrust`) totally trusts and values it — with a modest
row, so this is not an instance of the immodest collapse.
Source: [[Deference Done Better]] §2 l. 157, fn 25 (the corrected Theorem 7.4 paraphrase)
Kind: N+
Fidelity: n/a -/
theorem chainQ_nested_trust_value :
    chainQ.Nested ∧ chainQ.toFrame.ModestAt 1 ∧ Trust chainQ.μ chainQ.toFrame ∧
      TotalTrust chainQ.μ chainQ.toFrame ∧ Value chainQ.μ chainQ.toFrame :=
  have htt := chainQ.totalTrust_of_nested_of_simpleTrust chainQ_nested chainQ_simpleTrust
  ⟨chainQ_nested, chainQ_modestAt1, htt.trust chainQ.μ_mem.1, htt,
    (value_iff_totalTrust chainQ.μ_mem _).2 htt⟩

/-! ## A separate deferrer on `chainQ`: Simple Trust is not enough -/

/-- The deferrer `π = (½, 1/5, 3/10)`.
Source: none: new (repair round 2)
Kind: D
Fidelity: n/a -/
def chainπ : Fin 3 → ℝ := ![1 / 2, 1 / 5, 3 / 10]

/-- It is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem chainπ_mem : chainπ ∈ stdSimplex ℝ (Fin 3) := by
  refine ⟨fun w => ?_, ?_⟩
  · fin_cases w <;> norm_num [chainπ, vec3_two, fin3_mk_two]
  · norm_num [Fin.sum_univ_three, chainπ, vec3_two]

set_option maxHeartbeats 1000000 in
/-- `π` simply trusts `chainQ` (brute force as for the prior).
Source: none: new (repair round 2)
Kind: N+
Fidelity: n/a -/
theorem chainQ_simpleTrust_π : SimpleTrust chainπ chainQ.toFrame := by
  intro q t hpos
  obtain ⟨h0, h1, h2⟩ := chainQ_P
  have hE : ∀ w, w ∈ chainQ.toFrame.probEvent q t ↔ t ≤ mass (chainQ.toFrame.P w) q := by
    intro w; simp [Frame.probEvent]
  simp only [massFin3, mem_inter, hE, h0, h1, h2, chainπ, Matrix.cons_val_zero,
    Matrix.cons_val_one, vec3_two] at hpos ⊢
  by_cases h0q : (0 : Fin 3) ∈ q <;> by_cases h1q : (1 : Fin 3) ∈ q <;>
    by_cases h2q : (2 : Fin 3) ∈ q <;>
    simp only [h0q, h1q, h2q, if_true, if_false, true_and, false_and, and_true, and_false,
      add_zero, zero_add, mul_zero, mul_one, not_false_eq_true, not_true_eq_false] at hpos ⊢ <;>
    (try norm_num at hpos ⊢) <;>
    (first
      | linarith
      | (split_ifs at hpos ⊢ <;> (first | linarith | (norm_num at hpos ⊢ <;> linarith))))

/-- `π` does not totally trust `chainQ`: at `X = (0, 1, −1)`, `s = 0` every row's estimate is
`≥ 0` and the product sum is `π(1) − π(2) = −1/10`.
Source: none: new (repair round 2)
Kind: N+
Fidelity: n/a -/
theorem chainQ_not_totalTrust_π : ¬ TotalTrust chainπ chainQ.toFrame := by
  intro h
  obtain ⟨h0, h1, h2⟩ := chainQ_P
  have hsum := h ![0, 1, -1] 0
  rw [Fin.sum_univ_three] at hsum
  norm_num [E, Fin.sum_univ_three, vec3_two, fin3_mk_two, h0, h1, h2, chainπ] at hsum

/-- `π` does not value `chainQ` (Theorem 2.2).
Source: none: new (repair round 2)
Kind: N+
Fidelity: n/a -/
theorem chainQ_not_value_π : ¬ Value chainπ chainQ.toFrame := fun h =>
  chainQ_not_totalTrust_π ((value_iff_totalTrust chainπ_mem _).1 h)

/-- `π` does not trust `chainQ`: at `q = {1}`, `p = {1, 2}`, `t = ½` the conditioning event is
`{1, 2}` (row 0 gives `p` probability `0` and is excluded; rows 1, 2 have `P(1 | {1,2}) = 1, ½`),
so Trust asks `½ · π({1,2}) = ¼ ≤ π(1) = 1/5`, which fails.
Source: none: new (repair round 2)
Kind: N+
Fidelity: n/a -/
theorem chainQ_not_trust_π : ¬ Trust chainπ chainQ.toFrame := by
  intro h
  obtain ⟨h0, h1, h2⟩ := chainQ_P
  have hev : chainQ.toFrame.condProbEvent {1} {1, 2} (1 / 2) = {1, 2} := by
    ext w
    rw [Frame.condProbEvent, mem_filter]
    fin_cases w <;> simp [h0, h1, h2, massFin3, vec3_two, fin3_mk_two] <;> norm_num
  have := h {1} {1, 2} (1 / 2) (by rw [hev]; norm_num [massFin3, chainπ, vec3_two, Fin.ext_iff])
  rw [hev] at this
  norm_num [massFin3, chainπ, vec3_two, Fin.ext_iff] at this

/-- **On a nested prior frame a separate deferrer's Simple Trust does not imply Value** (nor
Trust): the OPEN `prior_trust_value_all_nested_open` genuinely needs Trust's conditional tests,
whereas for the prior itself Simple Trust suffices (`chainQ_nested_trust_value`).
Source: none: new (repair round 2; a boundary of the OPEN separate-deferrer statement)
Kind: N+
Fidelity: n/a -/
theorem chainQ_simpleTrust_not_value :
    chainQ.Nested ∧ SimpleTrust chainπ chainQ.toFrame ∧ ¬ Trust chainπ chainQ.toFrame ∧
      ¬ Value chainπ chainQ.toFrame :=
  ⟨chainQ_nested, chainQ_simpleTrust_π, chainQ_not_trust_π, chainQ_not_value_π⟩

/-! ## `diracQ`: the finest partition (audit r2 Q5, copied) -/

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The prior frame with `E_w = {w}`: the expert knows the world.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q5
Kind: D
Fidelity: n/a -/
def diracQ (μ : W → ℝ) (hpos : ∀ w, 0 < μ w) (hsum : ∑ w, μ w = 1) : PriorFrame W :=
  ⟨μ, hpos, hsum, fun w => {w}, fun w => singleton_nonempty w⟩

/-- Its rows are the point masses.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q5
Kind: L
Fidelity: n/a -/
theorem diracQ_P (μ : W → ℝ) (hpos : ∀ w, 0 < μ w) (hsum : ∑ w, μ w = 1) (w : W) :
    (diracQ μ hpos hsum).toFrame.P w = fun v => if v = w then 1 else 0 := by
  funext v
  show (if v ∈ ({w} : Finset W) then μ v / mass μ {w} else 0) = if v = w then 1 else 0
  by_cases h : v = w
  · subst h; simp [mass_singleton, (hpos v).ne']
  · simp [h]

/-- Its cells are singletons.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q5
Kind: L
Fidelity: n/a -/
theorem diracQ_cell (μ : W → ℝ) (hpos : ∀ w, 0 < μ w) (hsum : ∑ w, μ w = 1) (w : W) :
    (diracQ μ hpos hsum).toFrame.cell ((diracQ μ hpos hsum).toFrame.P w) = {w} := by
  ext v
  rw [Frame.mem_cell, mem_singleton, diracQ_P, diracQ_P]
  constructor
  · intro h
    by_contra hne
    have := congrFun h w
    simp [Ne.symm hne] at this
  · rintro rfl; rfl

/-- The frame is immodest.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q5
Kind: L
Fidelity: n/a -/
theorem diracQ_immodest (μ : W → ℝ) (hpos : ∀ w, 0 < μ w) (hsum : ∑ w, μ w = 1) :
    (diracQ μ hpos hsum).toFrame.Immodest := by
  intro w
  rw [Frame.selfMass, diracQ_cell, mass_singleton, diracQ_P]
  simp

/-- The frame is nested (singletons that meet coincide).
Source: none: new (repair round 2)
Kind: L
Fidelity: n/a -/
theorem diracQ_nested (μ : W → ℝ) (hpos : ∀ w, 0 < μ w) (hsum : ∑ w, μ w = 1) :
    (diracQ μ hpos hsum).Nested := by
  intro v w hne
  obtain ⟨x, hx⟩ := hne
  change x ∈ ({v} : Finset W) ∩ {w} at hx
  rw [mem_inter, mem_singleton, mem_singleton] at hx
  left
  change ({v} : Finset W) ⊆ {w}
  rw [← hx.1, hx.2]

/-- The prior reflects it.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q5
Kind: L
Fidelity: n/a -/
theorem diracQ_reflects (μ : W → ℝ) (hpos : ∀ w, 0 < μ w) (hsum : ∑ w, μ w = 1) :
    Reflects μ (diracQ μ hpos hsum).toFrame := by
  intro ρ hρ v
  obtain ⟨w, _, rfl⟩ := Frame.mem_cands.1 hρ
  rw [diracQ_cell, mass_singleton, diracQ_P]
  simp only [ind, mem_singleton]
  split_ifs with h
  · rw [h]
  · ring

/-- **The nested theorem's antecedent and consequent are both satisfiable**: on the finest
partition the prior trusts and values the induced frame (through the collapse, and equally
through `prior_value_of_trust_of_nested`).
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q5
Kind: N+
Fidelity: n/a -/
theorem diracQ_trust_and_value (μ : W → ℝ) (hpos : ∀ w, 0 < μ w) (hsum : ∑ w, μ w = 1) :
    Trust μ (diracQ μ hpos hsum).toFrame ∧ Value μ (diracQ μ hpos hsum).toFrame := by
  have hμ : μ ∈ stdSimplex ℝ W := ⟨fun w => (hpos w).le, hsum⟩
  have t := tfae_immodestFrame hμ (diracQ_immodest μ hpos hsum)
  exact ⟨(t.out 0 3).1 (diracQ_reflects μ hpos hsum), (t.out 0 5).1 (diracQ_reflects μ hpos hsum)⟩

/-- **The separate-deferrer statement holds on the finest partition**, for every deferrer, by
the collapse: a positive instance of the OPEN `prior_trust_value_all_nested_open`.
Source: [[lit-ddb-facts-audit-r2-adversarial]] Q5
Kind: N+
Fidelity: n/a -/
theorem diracQ_open_all (μ : W → ℝ) (hpos : ∀ w, 0 < μ w) (hsum : ∑ w, μ w = 1) {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) (h : Trust π (diracQ μ hpos hsum).toFrame) :
    Value π (diracQ μ hpos hsum).toFrame :=
  ((tfae_immodestFrame hπ (diracQ_immodest μ hpos hsum)).out 3 5).1 h

end

end Cleanroom.Lit.LitDdbFacts.ExamplesPrior
