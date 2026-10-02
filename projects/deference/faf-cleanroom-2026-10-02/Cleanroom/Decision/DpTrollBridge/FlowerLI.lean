/-
  Soto's flower obstruction at the LI level, from a quotation portfolio (repair round 1).

  Target 11 of [[dp-troll-bridge-mandate]]. `flower_liminf_open` (`LILesion.lean`) states the
  obstruction unconditionally and is OPEN; this file proves it **conditional on the
  quotation mechanism** — a polynomial affine portfolio for the gated product
  `ctsInd (width n) p (P n (S n)) · (1 − P n (S n))` together with its per-world value law —
  which is exactly the object FAF's `paradoxResistanceQuoteOfDiagonal`
  (`Construction/Quotation/Packages.lean`) builds from a `MarketComputation` and an
  arithmetic fixed point, and which FAF's `lic_paradox_resistance` takes as the field
  `lower_affine` of its `ParadoxResistanceQuote`. The one thing FAF's package *assumes* about
  the certificate that the flower's reflection can *supply* is `theory_coherent` (the gated
  product's value vanishes in every completed-theory world); it is derived here from the
  reflection `S n ↔ (p ≤ P n (S n) → ψ n)`, and `ψ` plays no role — the obstruction does not
  depend on what the sentence promises above `p`.

  Imports `Properties.Introspection` (for `CompletedAffineQuoteEq`, `ctsInd`), which is
  heavier than `LILesion.lean`'s imports; kept in its own file.
-/

import LogicalInduction.Properties.Introspection

open LO
open LogicalInduction
open scoped LogicalInduction
open Filter Topology

namespace Cleanroom.Decision.DpTrollBridge

/-- The continuous threshold gate vanishes when its first argument does not exceed its
second (re-proof of FAF's `ctsInd_eq_zero_of_le`, which lives under `Construction/Quotation`
and is not imported here).
Source: none: infrastructure (FAF `ctsInd_eq_zero_of_le`, `Construction/Quotation/DeferralFibre.lean`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
lemma ctsInd_eq_zero_of_le' (δ : ℚ) (x y : ℝ) (hδ : 0 < δ) (hxy : x ≤ y) :
    ctsInd δ x y = 0 := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold ctsInd
  have hratio : (x - y) / (δ : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδR.le
  rw [max_eq_left hratio, min_eq_right zero_le_one]

/-- **The flower obstruction's lower bound, from a quotation portfolio.** Let `S n` be
reflected in every completed-theory world as `S n ↔ (p ≤ P n (S n) → ψ n)`, and let `port`
be a polynomial affine portfolio (FAF's `AffineQuotePortfolio`) for the gated product
`ctsInd (width n) p (P n (S n)) · (1 − P n (S n))` whose per-world value is
`scale · ctsInd (…) · (1 − w (S n))` (`hvalue`), with the gate width `→ 0`. Then for every
`ε > 0`, eventually `p − ε ≤ P n (S n)`: `liminf P n (S n) ≥ p`.
Proof: the portfolio's value vanishes in every completed-theory world — when
`P n (S n) < p` the reflection's antecedent fails, so `S n` holds there and `1 − 1[S n] = 0`;
when `p ≤ P n (S n)` the gate is `0` (`ctsInd_eq_zero_of_le'`) — so it is a
`CompletedAffineQuoteEq` and FAF's `gap_asympEq_zero` (affine provability induction at
`b := 0`) gives the gated product `→ 0` on the diagonal; if the price sat below `p − ε` with
`width n < ε` the gate would be `1` and the product `≥ 1 − p > 0`. This is the lower half of
FAF's `lic_paradox_resistance` with the flower's reflection in place of the diagonal's.
`ψ` is unused: the obstruction is independent of what `S` promises above the threshold.
What is **not** built: the portfolio itself (the EF-gated family with its machine-metered
emission), which FAF constructs for the paradox sentence from a `MarketComputation` and an
arithmetic fixed point under `Construction/Quotation`; that construction is the remaining
obligation of `flower_liminf_open`.
Source: Soto 2023 "Argmaxing our strategy" p. 3 (Picking flowers); [[bli-soto-b-inventory]] 004; [[dp-troll-bridge-mandate]] target 11; repair round 1
Kind: C
Fidelity: weaker: conditional on the quotation portfolio; otherwise the inventory's precise reading (eventual `p − ε` form of `liminf ≥ p`)
Hyps: (c) `hrefl` is the self-referential sentence's reflection in the theory; (c) `port` + `hvalue` is the quotation mechanism (a polynomial affine portfolio for the gated product with its per-world value law), the object FAF's `paradoxResistanceQuoteOfDiagonal` constructs and `lic_paradox_resistance` assumes -/
theorem flower_liminf_of_portfolio (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (p : ℚ) (hp1 : p < 1)
    (S ψ : ℕ → Sentence)
    (width : ℕ → ℚ) (hwidth_pos : ∀ n, 0 < width n)
    (hwidth_zero : Tendsto (fun n => (width n : ℝ)) atTop (𝓝 0))
    (hrefl : ∀ n, ∀ v : PCWorld, v.ConsistentWithTheory DP →
      (v.Holds (S n) ↔ ((p : ℝ) ≤ P n (S n) → v.Holds (ψ n))))
    (port : AffineQuotePortfolio P
      (fun n => ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - P n (S n))))
    (hvalue : ∀ n (w : Valuation), (port.family n).value P w =
      (port.scale : ℝ) * (ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - w (S n))))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, (p : ℝ) - ε ≤ P n (S n) := by
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    fun n s => IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n s
  have hcoh : ∀ n (v : PCWorld), v.ConsistentWithTheory DP →
      (port.family n).value P v.payout = 0 := by
    intro n v hv
    rw [hvalue]
    by_cases hlt : P n (S n) < (p : ℝ)
    · have hS : v.Holds (S n) :=
        (hrefl n v hv).mpr (fun hle => absurd hle (not_le.mpr hlt))
      simp [PCWorld.payout, hS]
    · have h0 : ctsInd (width n) (p : ℝ) (P n (S n)) = 0 :=
        ctsInd_eq_zero_of_le' (width n) _ _ (hwidth_pos n) (not_lt.mp hlt)
      simp [h0]
  let q : CompletedAffineQuoteEq P DP
      (fun n => ctsInd (width n) (p : ℝ) (P n (S n)) * (1 - P n (S n))) := ⟨port, hcoh⟩
  have hgap := q.gap_asympEq_zero hworld
  have hp1R : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hμ : (0 : ℝ) < 1 - p := sub_pos.mpr hp1R
  intro ε hε
  have hwidth : ∀ᶠ n in atTop, (width n : ℝ) < ε := hwidth_zero (Iio_mem_nhds hε)
  have hnear := asympEq_iff_eventuallyWithin.1 hgap ((1 - p) / 2) (by linarith)
  filter_upwards [hwidth, hnear] with n hw hn
  by_contra hnot
  have hprice : P n (S n) < (p : ℝ) - ε := by linarith
  have hgate : ctsInd (width n) (p : ℝ) (P n (S n)) = 1 :=
    ctsInd_eq_one_of_le_sub (width n) (p : ℝ) (P n (S n)) (hwidth_pos n) (by linarith)
  simp only [sub_zero] at hn
  rw [hgate, one_mul, abs_of_nonneg (by linarith [(hP n (S n)).2])] at hn
  linarith

end Cleanroom.Decision.DpTrollBridge
