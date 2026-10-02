import Cleanroom.Found.LiQuoteLane.Defs

/-!
# Audit round 3 (adversarial) probe: the ledger payload is at least the *fourth* power of the code

The OPEN `B.exists_fuelDominated` (repair round 2) argues that a witness of the repaired
`FuelDominated` is a fuel-calculus construction, and sizes the room available by "the payload is
at least `c²` (`Nat.pair j c ≥ c²`)". The payload is `Nat.pair n (Nat.pair j c)`, and `Nat.pair a b ≥
b²` for every `a`, so the payload is at least `c⁴`, and the route's clock at the payload,
`(p + 1)² + 1`, is above `c⁸`. The arithmetic of the OPEN's docstring understates the room by a
square; the direction of the understatement is favourable to the OPEN being inhabited (a polarity
program has fuel `> c⁸` and may use intermediate values up to `(p + 1)²` on a code of size `c`).
Not imported by the library.
-/

namespace Cleanroom.Li.LiCoupledPair.AuditR3

open Cleanroom.Found.LiQuoteLane

/-- `Nat.pair a b ≥ b * b` for every `a`. -/
theorem sq_le_pair (a b : ℕ) : b * b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · exact Nat.le_add_right _ _
  · have hab : b ≤ a := Nat.le_of_not_lt h
    exact le_trans (Nat.mul_le_mul hab hab)
      (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

/-- The ledger payload `⟨n, ⟨j, c⟩⟩` is at least `c ^ 4`. -/
theorem pow_four_le_ledgerPayload (j n c : ℕ) : c ^ 4 ≤ ledgerPayload j n c := by
  unfold ledgerPayload
  have h1 : c * c ≤ Nat.pair j c := sq_le_pair j c
  have h2 : Nat.pair j c * Nat.pair j c ≤ Nat.pair n (Nat.pair j c) := sq_le_pair n _
  calc c ^ 4 = (c * c) * (c * c) := by ring
    _ ≤ Nat.pair j c * Nat.pair j c := Nat.mul_le_mul h1 h1
    _ ≤ Nat.pair n (Nat.pair j c) := h2

end Cleanroom.Li.LiCoupledPair.AuditR3
