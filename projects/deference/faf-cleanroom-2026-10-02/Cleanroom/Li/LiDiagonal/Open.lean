import Cleanroom.Li.LiDiagonal.Paper

/-!
# `li-diagonal` · Open: the two open statements (T7e, E2)

Precise Lean statements of the package's two deliberately open questions, each with `sorry`,
listed in `run/wp/li-diagonal/li-diagonal-open.txt`. Nothing in the package rests on them.

* **T7e** (trust-lab-058): is the truth stream of FAF's diagonal, `𝟙[P_n(ψ_n) < p]`, a
  `PseudorandomFrequency` at `p` relative to the market that generates it? The converse
  (pseudorandom ⟹ price `→ p`) is FAF's `lic_learning_pseudorandom_frequency`; T1 says the sides
  sit below every e.c. resolution of the price; the direct question is the crux and is **open**
  (the statement below may be false: nothing here is evidence either way).
* **E2**: beyond e.c. rates — does the paper market's price of its Kleene diagonal sit *exactly*
  at `p` from some day on? (The alternative, `|P_n(ψ_n) − p| ≥ η_n` infinitely often for some
  computable `η → 0`, relates to the paper's Uncomputable Convergence Rates, `li-projection`'s
  extension.) **Open**; the statement below is the positive form and may be false.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Propositional
open Filter Topology

/-- **T7e (OPEN).** The diagonal's truth stream `𝟙[P_n(ψ_n) < p]` is pseudorandom at frequency
`p` along `f`, relative to the market `P` itself. Open: neither proved nor refuted here.
Scope: single-market; threshold `p`, deferral `f`; FAF's Kleene diagonal.
Source: [[trust-lab-inventory]] 058; [[li-diagonal-mandate]] T7e
Kind: OPEN
Fidelity: exact (the question as posed)
Hyps: n/a -/
theorem diagonal_sides_pseudorandom {DP : DeductiveProcess} {T : ArithmeticTheory} [𝗜𝚺₁ ⪯ T]
    (Q : QuotationTheoryPresentation DP T) (P : History) [IsLogicalInductor P DP]
    (market : MarketComputation P) (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (f : DeferralFunction) :
    PseudorandomFrequency (diagTruth P (kleeneDiag T market p) p) (p : ℝ) f P := by
  sorry

/-- **E2 (OPEN).** On the paper market, the price of its Kleene diagonal is exactly `p` from some
day on. Open in both directions: neither this nor its negation (`|P_n(ψ_n) − p| ≥ η_n` infinitely
often for some computable `η → 0`) is established here.
Scope: single-market; threshold `p`; FAF's Kleene diagonal over the paper market.
Source: [[li-diagonal-mandate]] E2; LI paper §5.5.1 (Uncomputable Convergence Rates)
Kind: OPEN
Fidelity: exact (the positive form of the question)
Hyps: n/a -/
theorem paper_kleene_exact_pinning (T : ArithmeticTheory) [T.Δ₁] [Entailment.Consistent T]
    [𝗜𝚺₁ ⪯ T] (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ᶠ n in atTop,
      liaHistory (paperDP T) n (kleeneDiag T (paperMarketComputation T) p n) = (p : ℝ) := by
  sorry

end Cleanroom.Li.LiDiagonal
