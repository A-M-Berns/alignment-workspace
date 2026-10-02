import Cleanroom.Fa.FaTheoremA.Defs

/-!
# fa-theorem-a · audit r2 (adversarial) probe: `hE01` does not force a price-independent day-set

`lemmaP`'s Fidelity line (and the ledger row, after repair round 1) says: "an `EF` denotes a
continuous function of the day's prices, so a `{0,1}`-valued one is constant in the prices on
each day — `hE01` forces `E` to be a price-independent day-set". But `hE01` is
`∀ n, (E n).denote A = 0 ∨ (E n).denote A = 1` — a statement about the denotation at the *one*
history `A`, not at every valuation. Witness: the package's own upper gate `quoteRampAbove Y 0 1`
is generable (T2), denotes `0` on every day at the all-zero history (so `hE01` holds there), and
denotes `1/2` on every day at the all-`1/2` history — it is price-dependent. The Lean `lemmaP`
is therefore *stronger* than "e.c. day-set" (it admits any generable gate whose realized weights
are `{0,1}`); the Fidelity line's justification is wrong, not the theorem.
-/

namespace Cleanroom.Fa.FaTheoremA.AuditR2

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Fa.FaTheoremA

/-- The constant-price history (not an inductor; only the denotation is at issue). -/
noncomputable def constHist (r : ℝ) : History := fun _ _ => r

/-- `𝔼_n(Y)` at a constant-price history is that constant. -/
lemma expect_constHist (r : ℝ) (Y : LUV) (n : ℕ) : Y.expect (constHist r) n = r := by
  simp only [LUV.expect, LUV.expectApprox, constHist, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have h : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- At the all-zero history the gate `Ind_1(a_n > 0)` is `0` on every day: `hE01` holds. -/
theorem gate_hE01_at_zero (Y : ℕ → LUV) (n : ℕ) :
    (quoteRampAbove Y 0 1 n).denote (constHist 0) = 0 ∨
      (quoteRampAbove Y 0 1 n).denote (constHist 0) = 1 := by
  left
  rw [quoteRampAbove_denote Y (by norm_num), expect_constHist]
  simp [ctsInd]

/-- At the all-`1/2` history the same gate denotes `1/2`: it is not price-independent. -/
theorem gate_price_dependent (Y : ℕ → LUV) (n : ℕ) :
    (quoteRampAbove Y 0 1 n).denote (constHist (1 / 2)) = 1 / 2 := by
  rw [quoteRampAbove_denote Y (by norm_num), expect_constHist]
  simp [ctsInd]
  norm_num

/-- And it is generable, so it meets every `E`-hypothesis of `lemmaP` at the all-zero history. -/
example (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) :
    PGenerableWeighting (quoteRampAbove Y 0 1) :=
  quoteRampAbove_pgenerable Y hY 0 1

#print axioms gate_price_dependent

end Cleanroom.Fa.FaTheoremA.AuditR2
