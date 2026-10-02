import Cleanroom.Bli.BliTransfer.AttemptA.WitnessLia

/-!
# `bli-transfer` · audit round 1 · adversarial lens · probe: the T1.5 overlay is the LIA on
every day `≥ 1`, and its bodies are price-free

**Not imported by the library.** (Heavy: imports the construction through attempt A's
`WitnessLia`.) The witness map `wExpr` fires on day `0` only, so `overlay (liaHistory DP) (wOv
DP)` agrees with `liaHistory DP` on every day `≥ 1` and every sentence; and every fired body is
price-free. The witness therefore inhabits T1 at a re-pricing that is (i) a day-`0`-only,
(ii) constant-valued perturbation — infinite support (the family), so not FAF's finite-support
case, but the "expressible in the day's small prices" content of the overlay theorem is
exercised only at a constant.
-/

namespace BliTransferAuditR1

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliTransfer.AttemptA

/-- The witness map never fires after day `0`. -/
theorem wExpr_none_of_ne_zero (k : ℕ) (ψ : Sentence) (hk : k ≠ 0) : wExpr k ψ = none := by
  cases ψ <;> simp [wExpr, hk]

/-- The witness overlay is the LIA on every day `≥ 1`. -/
theorem overlay_eq_lia_of_ne_zero (DP : DeductiveProcess) (k : ℕ) (hk : k ≠ 0) (ψ : Sentence) :
    overlay (liaHistory DP) (wOv DP) k ψ = liaHistory DP k ψ := by
  by_cases hs : SmallOn k ψ
  · exact overlay_small hs
  · rw [overlay_large hs]
    rcases (wMap DP).silent k ψ (wExpr_none_of_ne_zero k ψ hk) with h | h
    · exact h
    · exact absurd h hs

/-- Every fired body of the witness map is price-free. -/
theorem wExpr_body_priceFree (k : ℕ) (ψ : Sentence) (e : EF) (h : wExpr k ψ = some e) :
    e.priceQueries = [] := by
  cases ψ with
  | atom a =>
      simp only [wExpr_atom] at h
      split_ifs at h with hc
      · obtain rfl := Option.some.inj h
        simp [EF.priceQueries]
  | falsum => simp [wExpr] at h
  | imp _ _ => simp [wExpr] at h
  | and _ _ => simp [wExpr] at h
  | or _ _ => simp [wExpr] at h

end BliTransferAuditR1
