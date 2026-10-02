import Cleanroom.Li.LiCoupledPair.A.Open

/-!
# Audit round 3 (adversarial) probe: the pinned `sib` conjunct really yields `Y n = sib n (F n) (P n)`

Repair round 2 (audit r2 adversarial N1) added to both sealed existence statements the conjunct
`S.sib = fun N => liaHistory (siblingProcess S.base S.a S.e N)` and the ledger says that "at every
system of record `Y n = sib n (F n) (contract n)`". The carrier's `Y_eq` pins `Y n` to FAF's
`liaQuote` on the frozen process (a rational), while `sib n` is a `History` (real-valued), so the
claim is an identity across the cast `liaHistory_eq_quote_cast` (`rfl` in FAF). This probe checks
that the claim is derivable from the pinned statement as shipped, for every inhabitant of the
pinned shape and at `sealedSystem_exists_of_uniform`. Not imported by the library.
-/

namespace Cleanroom.Li.LiCoupledPair.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-- Any sealed system whose siblings are pinned to FAF's LIA on the frozen processes settles the
contract to the sibling's own day-`F n` price of `contract n` (as a real). -/
theorem Y_eq_sib (S : SealedSiblingSystem)
    (hsib : S.sib = fun N => liaHistory (siblingProcess S.base S.a S.e N)) (n : ℕ) :
    (S.Y n : ℝ) = S.sib n (S.F.f n) (S.contract n) := by
  simp only [S.Y_eq n, hsib, liaHistory_eq_quote_cast]

/-- At the proved conditional form: the corpus's `Y_n := H^{[n]}_{F(n)}(P^{(n)})` with `H^{[n]}`
the field `sib n` itself. -/
theorem sealedSystem_exists_of_uniform_Y_sib (hU : UniformLIAEvaluator) :
    ∃ S : SealedSiblingSystem, S.base = paperDP 𝗜𝚺₁ ∧ S.DPA0 = paperDP 𝗜𝚺₁ ∧
      S.F = succDeferral ∧ S.contract = witnessQuoted 0 ∧
      ∀ n, (S.Y n : ℝ) = S.sib n (S.F.f n) (S.contract n) := by
  obtain ⟨S, h1, h2, -, h4, -, -, h7, h8⟩ := A.sealedSystem_exists_of_uniform hU
  exact ⟨S, h1, h2, h4, h7, fun n => Y_eq_sib S h8 n⟩

end Cleanroom.Li.LiCoupledPair.AuditR3
