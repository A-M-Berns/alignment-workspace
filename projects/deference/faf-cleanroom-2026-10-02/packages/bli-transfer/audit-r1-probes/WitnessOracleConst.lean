import Cleanroom.Bli.BliTransfer.AttemptA.WitnessOracle

/-!
# `bli-transfer` · audit round 1 · adversarial lens · probe: the witness certificate is the
constant special case

**Not imported by the library.** The only `SpliceCertificate` instance in the package
(`wCertificate`, oracle `wOracle`) (1) fires on day `0` only, (2) emits one fixed price-free body
`wBody = [1, ⌜1/2⌝]` whenever it fires, and (3) has a *constant* output budget
(`R_poly = C wOut.length`, degree `0`). So the certificate's one new feature over FAF's freeze
`RunOracle` — a polynomial, non-constant output bound for a body that reads small prices — is
not exercised by any instance in this package.
-/

namespace BliTransferAuditR1

open LogicalInduction Cleanroom.Bli.BliTransfer.AttemptA

/-- The lookup is silent on every day other than `0`. -/
theorem wExprRun_none_of_ne_zero (b : List ℕ) (D : ℕ) (hD : D ≠ 0) : wExprRun b D = none := by
  simp [wExprRun, hD]

/-- Whenever the lookup fires, the body is the fixed word `wBody`. -/
theorem wExprRun_body (b : List ℕ) (D : ℕ) (raw : List ℕ) (h : wExprRun b D = some raw) :
    raw = wBody := by
  by_cases hc : D = 0 ∧ familyRun b = true
  · simp [wExprRun, hc] at h
    exact h.symm
  · simp [wExprRun, hc] at h

/-- The oracle's output budget is a constant polynomial. -/
theorem wOracle_R_poly_natDegree : wOracle.R_poly.natDegree = 0 := by
  simp [wOracle]

end BliTransferAuditR1
