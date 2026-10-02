import Cleanroom.Found.LiQuoteLane.Readability

/-!
# Audit round 3 (fidelity) probe: the converse of `readability_ofApprox`

Not imported by the library. Question: findings F2 and the report's "Push further" say that over
FAF "L4 needs (L)'s counterpart exactly when the table is not asymptotically approximable by a
generable sequence". `readability_ofApprox` gives one direction (a `P`-generable approximant
suffices). This probe checks the other: for a reader whose day-`n` estimates of the ledger LUV
are rational (every LIA), the reader's *own estimate* `𝔼^P_n(α_{j,n})` is a `P`-generable
sequence (`ledgerFeature`, T4.2), so L4 holding is *equivalent* to the existence of a
`P`-generable asymptotic approximant. Consequence: for rational-priced readers the (c) `hz` of
`readability_ofApprox` is exactly the content of L4 — it cannot be discharged for the LIA instance
without proving L4 — and the OPEN `readability_fails_without_generability` is equivalently "some
inductor over some ledger process whose table has no `P`-generable asymptotic approximant".
-/

namespace Cleanroom.Found.LiQuoteLane.AuditR3Fid

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- If the reader's estimates of item `j`'s ledger LUV are rational and L4 holds, the estimate
itself is a `P`-generable approximant of the table (through `ledgerFeature`, T4.2). -/
theorem approximant_of_readability (P : History) (a : ℕ → ℕ → ℚ) (j : ℕ)
    (hrat : ∀ n, ∃ q : ℚ, (ledgerLuv j n).expect P n = q)
    (h : (fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ))) :
    ∃ zhat : ℕ → ℚ, PGenerableRat P zhat ∧
      Tendsto (fun n => (zhat n : ℝ) - a j n) atTop (𝓝 0) := by
  choose zhat hz using hrat
  refine ⟨zhat, ⟨fun n => ledgerFeature j n,
    (ledgerFeature_pgenerable j).toGeneratedRatFeature fun n => ?_⟩, ?_⟩
  · rw [ledgerFeature_denote, hz n]
  · unfold AsympEq at h
    refine h.congr fun n => ?_
    simp only [hz n]

/-- **L4 iff a generable approximant exists**, for a rational-priced reader over a ledger process
(every stage satisfiable, `[0,1]` table). -/
theorem readability_iff_approximant (P : History) (base : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) [IsLogicalInductor P (ledgerProcess base a e)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess base a e).D n))
    (hmem : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1) (j : ℕ)
    (hrat : ∀ n, ∃ q : ℚ, (ledgerLuv j n).expect P n = q) :
    ((fun n => (ledgerLuv j n).expect P n) ≈ₙ (fun n => (a j n : ℝ))) ↔
      ∃ zhat : ℕ → ℚ, PGenerableRat P zhat ∧
        Tendsto (fun n => (zhat n : ℝ) - a j n) atTop (𝓝 0) :=
  ⟨approximant_of_readability P a j hrat,
   fun ⟨zhat, hz, hlim⟩ => readability_ofApprox P base a e hworld hmem j zhat hz hlim⟩

end Cleanroom.Found.LiQuoteLane.AuditR3Fid
