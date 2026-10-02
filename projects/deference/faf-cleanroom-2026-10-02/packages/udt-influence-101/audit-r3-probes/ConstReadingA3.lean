import Cleanroom.Udt.UdtInfluence101.Priv

/-!
# Audit r3 (adversarial) probe: under the constant-per-state reading of `Ā_{h,n}`, the same instance violates A3

Not imported by the library. One claim.

Finding F4 says Post 8's Theorem 1 is false under its stated assumptions, with `Ā_{h,n}` rendered as
the package does (an algorithm reading the unplannables up to time `n`, Post 6 §1.2 "destroy all of
its ability to entangle its behavior with incoming unplannable information *past n timesteps*"; the
diffuse predictor sees its timeline-average, Post 7 Sub-Assumption 4). The r1 adversarial audit (N3)
raised the alternative reading — from the actual time-`n` epistemic state, `Ā_{h,n}` is the *constant*
algorithm playing the number `μ_n = ℙ_{h₁:ₙ}(A(h, S̄_h) = ·|h)`. This probe records what happens to the
Priv instance under that alternative: Assumption 3's probability clause fails at `ω₀`
(`𝕀^ℙ_∅(privA, hT, full) = 0`, while the constant `δ one-box = privA(hT, S̄)(ω₀)` has `1/2`), so under
that reading the instance is outside Theorem 1's hypotheses rather than a counterexample to it. The
alternative reading also makes A3 at `n = |h|` say the predictor responds to `A` as to the constant
`A(h, S̄_h)(actual)`, i.e. knows the agent's actual mixed action — not Post 7's diffuse predictor —
which is why F4's reading is the better-supported one; but the sentence "not a matter of
interpretation" in `post8_theorem1_counterexample`'s docstring should carry this argument, and F4's
"false as stated" is a bridge claim about the source that needs the ATTRIBUTION-UNVETTED label.
-/

namespace Cleanroom.Udt.UdtInfluence101.AuditR3

open Cleanroom.Udt.UdtPolicyCalc
open Cleanroom.Udt.UdtInfluence101.Home (hT)
open Cleanroom.Udt.UdtInfluence101.Priv

noncomputable section

/-- Under the constant-per-state reading, `Ā_{hT,0}` at `ω₀` is `ofDist (privA(hT, S̄)(ω₀))`
`= δ one-box`, and A3's `𝕀^ℙ` clause fails there: `0 ≠ 1/2`. -/
theorem constReading_A3_fails :
    Priv.S.IP 0 privA hT true ω₀ ≠
      Priv.S.IP 0 (ofDist (Priv.S.play privA hT ω₀)) hT true ω₀ := by
  rw [IP_privA, play_privA_ω₀]
  have h : (ofDist (FinDist.delta true) : Alg Bool Bool Bool 2) = ofAct true := rfl
  rw [h, IP_ofAct_true]
  norm_num

end

end Cleanroom.Udt.UdtInfluence101.AuditR3
