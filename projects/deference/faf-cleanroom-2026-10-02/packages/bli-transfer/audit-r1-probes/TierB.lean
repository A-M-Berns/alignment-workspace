import Cleanroom.Bli.BliTransfer.Defs

/-!
# `bli-transfer` · audit round 1 · adversarial lens · probe: Tier B is real

**Not imported by the library.** Evidence for `bli-transfer-audit-r1-adversarial.md` § What I
checked (T1, trap (iv)). An `ExprMap` that never fires forces `overlay Q ov = Q`: the `silent`
field is a genuine hypothesis (an `ov` that moves an un-fired large sentence has no `ExprMap`),
and T1 at the never-firing map is literally `IsLogicalInductor Q DP` — the trivial instance,
which is why the N+ witness must fire somewhere (`overlay_ne_lia`).
-/

namespace BliTransferAuditR1

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliTransfer

/-- A never-firing expression map forces the overlay to be `Q` on every day and sentence. -/
theorem overlay_eq_of_never_fires {Q : History} {ov : ℕ → Sentence → ℚ}
    (E : ExprMap Q ov) (hnone : ∀ k ψ, E.expr k ψ = none) :
    overlay Q ov = Q := by
  funext k ψ
  by_cases hs : SmallOn k ψ
  · exact overlay_small hs
  · rw [overlay_large hs]
    rcases E.silent k ψ (hnone k ψ) with h | h
    · exact h
    · exact absurd h hs

end BliTransferAuditR1
