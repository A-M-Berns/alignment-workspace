import Cleanroom.Li.LiCoupledPair.A.Joint

/-!
# Audit round 3 (adversarial) probe: the two-way pair's `A`-side ledger records one value under every item

`SealedSiblingSystem`'s docstring discloses (repair round 1) that `A`'s process records `Y n` under
every item index `j` (consistent duplicates). The same holds for the two-way pair of record:
`aH P j n` ignores `j`, so `jointDPA P = ledgerProcess DPA0 (aH P) σ` records `H`'s single
realized expectation `𝔼^H_{f n}(XH n)` as `ledgerLuv j n` for every `j ≤ s` at stage `s` — consistent
duplicates, not several contracts. `TwoWayPair`'s docstring and ledger row do not say so (they
disclose only the family-3-on-both-sides point). Definitional (`rfl`); recorded for the row.
Not imported by the library.
-/

namespace Cleanroom.Li.LiCoupledPair.AuditR3

open Cleanroom.Li.LiCoupledPair.A

/-- The `A`-side table of the two-way pair does not depend on the item index. -/
theorem aH_indep_item (P : TwoWaySpec) (j j' n : ℕ) : aH P j n = aH P j' n := rfl

end Cleanroom.Li.LiCoupledPair.AuditR3
