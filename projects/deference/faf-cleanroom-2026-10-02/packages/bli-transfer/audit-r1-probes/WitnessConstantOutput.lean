import Cleanroom.Bli.BliTransfer.AttemptA.WitnessOracle

/-!
Audit r1 (fidelity) probe for `bli-transfer`: the witness of record for T1 (`wCertificate`, built
on `wOracle`) has a **constant-length** oracle output and a **price-free, constant** body
(`wExpr k ψ ∈ {none, some (const (1/2))}`). So the one clause that distinguishes the package's
certificate interface from FAF's freeze `RunOracle` — the polynomial (non-constant) output bound
`R_length_le` — is not exercised by any instance in this package, and neither is the
"expressible function of small prices" content of `ExprMap.leaves` (the witness body reads no
price). The witness is N+ for the theorem's hypothesis package (real inductor, price changed,
trader rewritten), and degenerate with respect to the certificate's new content; the ledger says
"day 0 only" and should say this too. Not imported by the library.
-/

namespace Cleanroom.Bli.BliTransfer.AuditR1

open LogicalInduction Cleanroom.Bli.BliTransfer.AttemptA

/-- The witness oracle's output is bounded by one constant on every input. -/
theorem wOracle_output_constant : ∃ c : ℕ, ∀ v : List Bool, (wOracle.R v).length ≤ c :=
  ⟨wOut.length, fun v => wOracleFn_length_le v⟩

/-- The witness lookup returns, on every run and every day, either nothing or the one fixed
body `wBody` (the oracle appends the `letE` close `8`) — no dependence on the run beyond the
family test. -/
theorem wExprRun_const (b : List ℕ) (D : ℕ) :
    wExprRun b D = none ∨ wExprRun b D = some wBody := by
  unfold wExprRun
  split_ifs <;> simp

end Cleanroom.Bli.BliTransfer.AuditR1
