import Cleanroom.Found.LiQuoteLane.Readability
import LogicalInduction.Construction.LIA

/-!
# Audit round 3 (adversarial) probe — `readability_ofApprox`'s hypothesis is equivalent to its
conclusion for every rational-priced reader

`readability_ofApprox` (the round-2 engine of T3.1) takes `hz : PGenerableRat P ẑ` for *some*
rational sequence `ẑ` with `ẑ_n − a_{j,n} → 0` and concludes `𝔼^P_n(α_{j,n}) ≈ₙ a_{j,n}`. For a
reader whose prices are rationals — every FAF `liaHistory` — the reader's *own* day-`n`
expectation of the ledger LUV is such a `ẑ`: `ledgerFeature j n` is a `PGenerableWeighting`
(T4.2) denoting it (`ledgerFeature_denote`). So the existential hypothesis is implied by the
conclusion (take `ẑ := 𝔼`), and the theorem is an iff (`readability_ofApprox_iff`).

This is **not** a squeeze: the forward direction is the criterion (provability induction), and
the instances with content are those where `ẑ` is given independently of `P` (`readability` at
`ẑ = a_j`, `readability_ofMachineApprox`, `readability_ofTendsto`). It is a characterization the
package could state: over a rational-priced reader, L4 holds at a table iff the table is
asymptotically approximable by a `P`-generable rational sequence. Not imported by the library.
-/

namespace Cleanroom.Found.LiQuoteLane.AuditR3Adv

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology
open Cleanroom.Found.LiQuoteLane

/-- A rational-priced history: every price is the cast of a rational. -/
def RationalPriced (P : History) : Prop := ∀ n φ, ∃ q : ℚ, P n φ = (q : ℝ)

/-- FAF's LIA is rational-priced (`liaHistory_eq_quote_cast`). -/
theorem liaHistory_rationalPriced (DP : DeductiveProcess) : RationalPriced (liaHistory DP) :=
  fun n φ => ⟨liaQuote DP n φ, liaHistory_eq_quote_cast DP n φ⟩

/-- The day-`n` expectation of the ledger LUV under a rational-priced reader is a rational. -/
lemma expect_rational {P : History} (hP : RationalPriced P) (j n : ℕ) :
    ∃ q : ℚ, (q : ℝ) = (ledgerLuv j n).expect P n := by
  classical
  choose q hq using hP n
  refine ⟨((n + 1 : ℕ) : ℚ)⁻¹ *
    ∑ i ∈ Finset.range (n + 1), q ((ledgerLuv j n).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))), ?_⟩
  simp only [LUV.expect, LUV.expectApprox, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast,
    Rat.cast_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (hq _).symm

/-- The reader's own expectation of the ledger LUV is a `P`-generable rational sequence:
`ledgerFeature j` denotes it. -/
theorem expect_pgenerable {P : History} (hP : RationalPriced P) (j : ℕ) :
    ∃ zhat : ℕ → ℚ, PGenerableRat P zhat ∧ ∀ n, (zhat n : ℝ) = (ledgerLuv j n).expect P n := by
  classical
  choose zhat hz using fun n => expect_rational hP j n
  refine ⟨zhat, ⟨fun n => ledgerFeature j n, ?_⟩, hz⟩
  have hw := ledgerFeature_pgenerable j
  exact { rank_le := hw.rank_le, polyTok := hw.polySeg, closed := hw.closed,
          denote := fun n => by
            show (ledgerFeature j n).denote P = (zhat n : ℝ)
            rw [ledgerFeature_denote]; exact (hz n).symm }

/-- **`readability_ofApprox` is an iff for rational-priced readers.** -/
theorem readability_ofApprox_iff (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ) (hP : RationalPriced P) :
    (∃ zhat : ℕ → ℚ, PGenerableRat P zhat ∧
        Tendsto (fun n => (zhat n : ℝ) - a j n) atTop (𝓝 0)) ↔
      (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ)) := by
  constructor
  · rintro ⟨zhat, hz, hlim⟩
    exact readability_ofApprox P base a e hworld hmem j zhat hz hlim
  · intro h
    obtain ⟨zhat, hz, hzeq⟩ := expect_pgenerable hP j
    refine ⟨zhat, hz, ?_⟩
    unfold AsympEq at h
    refine h.congr fun n => ?_
    rw [hzeq n]

/-- The same at FAF's LIA over any ledger process. -/
theorem readability_ofApprox_iff_lia (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule)
    [IsLogicalInductor (liaHistory (ledgerProcess base a e)) (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ) :
    (∃ zhat : ℕ → ℚ, PGenerableRat (liaHistory (ledgerProcess base a e)) zhat ∧
        Tendsto (fun n => (zhat n : ℝ) - a j n) atTop (𝓝 0)) ↔
      (fun n => (ledgerLuv j n).expect (liaHistory (ledgerProcess base a e)) n) ≈ₙ
        (fun n => (a j n : ℝ)) :=
  readability_ofApprox_iff _ base a e hworld hmem j (liaHistory_rationalPriced _)

end Cleanroom.Found.LiQuoteLane.AuditR3Adv
