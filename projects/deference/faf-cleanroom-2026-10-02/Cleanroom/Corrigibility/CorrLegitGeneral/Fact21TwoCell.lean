import Cleanroom.Corrigibility.CorrLegitGeneral.TwoCell
import Cleanroom.Found.LitDdbFrames.ExamplesFact21

/-!
# corr-legit-general — Fact 2.1's frame has two-cell local Trust and Value where global Total Trust fails

Adopted from the round-2 adversarial probe (`audit-r2-probes/Fact21TwoCell.lean`, repair round 2).
The mandate's T4(b) named "`fact21` at `q = {0}`" as the *failing* side of the two-cell
equivalence, and the ledger repeated it with `fact21_not_totalTrust` as the evidence. That claim
is false: at `q = {0}` the rows give `P_w(q) = 0.45, 0.15, 0.30` and `π21(q) = 0.17`, so both
Simple-Trust cuts hold at every threshold — two-cell local Total Trust w.r.t. `{q, ¬q}` **holds**
(`fact21_totalTrustWrt_q0`); the three masses are distinct, so the rows are determined by `P_w(q)`
and the package's two-cell theorem gives two-cell local Value too (`fact21_valuesWrt_q0`). What
fails on Fact 2.1's frame is *global* Total Trust, at the non-indicator bet `O₁ = (29, −3, −13)`
(`fact21_not_totalTrust`, cited), which says nothing about any two-cell question. Had the
mandate's sentence been true it would have refuted DDB's Fact 2.1 itself: Trust ⟹ Simple Trust
⟹ two-cell local Total Trust at every `q` (`forall_totalTrustWrt_questionOf_iff_simpleTrust`).
So `fact21` is the package's example of a frame with two-cell local Trust and Value at a `q` while
global Total Trust fails — locality is cheaper than global trust (findings F16).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Lit.LitDdbAccuracyMm

noncomputable section

/-- The two-cell question `{{0}, {1, 2}}` the mandate names.
Source: mandate T4(b) ("`fact21` at `q = {0}`")
Kind: D
Fidelity: exact -/
abbrev q0 : Finset (Fin 3) := {0}

/-- `π21` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π21_nonneg : ∀ w, 0 ≤ π21 w := by
  intro w; fin_cases w <;> norm_num [π21, vec3_two]

/-- The rows' masses of `q = {0}`: `0.45, 0.15, 0.30`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fact21_mass_q0 : mass (fact21.P 0) q0 = 45 / 100 ∧ mass (fact21.P 1) q0 = 15 / 100 ∧
    mass (fact21.P 2) q0 = 30 / 100 := by
  obtain ⟨h0, h1, h2⟩ := fact21_P
  refine ⟨?_, ?_, ?_⟩ <;> (rw [mass_singleton]; norm_num [h0, h1, h2])

/-- **Two-cell local Total Trust at `q = {0}` holds on Fact 2.1's frame** — the mandate's
"failing side" does not fail.
Source: [[Deference Done Better]] §2 Fact 2.1 l. 165 (the frame), §5 l. 398 (two-cell Total Trust
= Simple Trust); mandate T4(b) (its witness claim, refuted); audit r2 adversarial B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fact21_totalTrustWrt_q0 : TotalTrustWrt (questionOf q0) π21 fact21 := by
  rw [totalTrustWrt_questionOf_iff π21_nonneg]
  obtain ⟨m0, m1, m2⟩ := fact21_mass_q0
  constructor
  · intro t
    rw [mass_probEvent_eq, mass_inter_probEvent_eq]
    simp only [Fin.sum_univ_three, m0, m1, m2]
    simp +decide [π21, q0, vec3_two]
    split_ifs <;> (try norm_num) <;> (try linarith)
  · intro t
    rw [mass_probEventLE_eq, mass_inter_probEventLE_eq]
    simp only [Fin.sum_univ_three, m0, m1, m2]
    simp +decide [π21, q0, vec3_two]
    split_ifs <;> (try norm_num) <;> (try linarith)

/-- The rows are determined by `P_w(q)` (the three masses are distinct), so the two-cell Value
theorem's `hdet` holds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fact21_rows_det_q0 : ∀ w v, 0 < π21 w → 0 < π21 v →
    mass (fact21.P w) q0 = mass (fact21.P v) q0 → fact21.P w = fact21.P v := by
  obtain ⟨m0, m1, m2⟩ := fact21_mass_q0
  intro w v _ _ h
  fin_cases w <;> fin_cases v <;>
    first
      | rfl
      | (norm_num [m0, m1, m2] at h)

/-- **Two-cell local Value at `q = {0}` holds too**, by the package's two-cell theorem
(`valuesWrt_questionOf_of_simpleTrustOn` under `hdet`).
Source: [[Deference Done Better]] fn 65 (two-cell case, `TwoCell.lean`); audit r2 adversarial B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fact21_valuesWrt_q0 : ValuesWrt (questionOf q0) π21 fact21 :=
  valuesWrt_questionOf_of_simpleTrustOn π21_nonneg
    ((totalTrustWrt_questionOf_iff π21_nonneg).1 fact21_totalTrustWrt_q0) fact21_rows_det_q0

/-- **Packaged**: on Fact 2.1's frame, at `q = {0}` neither two-cell predicate fails, while global
Total Trust fails (`fact21_not_totalTrust`, cited, at the non-indicator bet `O₁`). Both cells of
the question have positive `π21`-mass (`0.17` and `0.83`), so this is not the one-cell trap.
Source: [[Deference Done Better]] §2 Fact 2.1 l. 165; mandate T4(b) (witness claim refuted,
findings F16); audit r2 adversarial B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fact21_q0_nothing_fails : TotalTrustWrt (questionOf q0) π21 fact21 ∧
    ValuesWrt (questionOf q0) π21 fact21 ∧ ¬ TotalTrust π21 fact21 ∧
    0 < mass π21 q0 ∧ 0 < mass π21 q0ᶜ := by
  refine ⟨fact21_totalTrustWrt_q0, fact21_valuesWrt_q0, fact21_not_totalTrust, ?_, ?_⟩
  · rw [mass_singleton]; norm_num [π21]
  · simp +decide [mass_eq_sum_ite, Fin.sum_univ_three, q0, π21, vec3_two]; norm_num

end

end Cleanroom.Corrigibility.CorrLegitGeneral
