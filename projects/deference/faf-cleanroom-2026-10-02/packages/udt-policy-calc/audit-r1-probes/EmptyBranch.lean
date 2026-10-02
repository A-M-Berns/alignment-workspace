import Cleanroom.Udt.UdtPolicyCalc.TransparentNewcomb

/-!
# Audit r1 (fidelity) probe: the empty branch of transparent Newcomb

Evidence for [[udt-policy-calc-audit-r1-fidelity]], non-blocking issue 1. The cited source of
`Transparent.edt_ne_udt_transparent` — [[when-udt-edt-diverge]] line 86 — says UDT "one-boxes
even facing the empty box". Against the model of record (gap1 §8, `Transparent.V`) that sentence
is false for every `0 < ε` (the policy optimum strictly two-boxes on `empty`) and a tie at `ε = 0`.
The EDT side of the separation is fixed by the payoff table alone (the prior enters only through
positivity of the conditioning events). Not imported by the library.
-/

namespace Cleanroom.Udt.UdtPolicyCalc.Transparent

/-- For every `0 < ε`, `(one, two)` strictly beats `(one, one)`: the policy optimum two-boxes on the
empty branch (margin `1000·ε`). -/
theorem probe_udt_twoBoxes_on_empty {ε : ℝ} (h0 : 0 < ε) :
    V ε (mk .one .one) < V ε (mk .one .two) := by
  rw [V_oneOne, V_oneTwo]
  linarith

/-- At `ε = 0` the two one-box-on-full policies tie: the source's "one-boxes even facing the empty
box" is at best indifference, never a strict preference. -/
theorem probe_tie_at_zero : V 0 (mk .one .one) = V 0 (mk .one .two) := by
  rw [V_oneOne, V_oneTwo]
  norm_num

/-- The EDT score at `(full, two)` is the table entry `1001000` for every full-support prior and
every `0 < ε ≤ 1`: the prior over the agent's own policy is load-bearing only through positivity. -/
theorem probe_edt_full_two_eq (μ : FinDist TPolicy) {ε : ℝ} (hμ : ∀ π, 0 < μ.w π) (h0 : 0 < ε)
    (h1 : ε ≤ 1) : edtScore μ ε .full .two = 1001000 :=
  edtScore_eq_of_pos (mass_full_two_pos hμ h0 h1)

/-- Likewise `(full, one)` is `1000000` for every full-support prior and `0 ≤ ε < 1`. -/
theorem probe_edt_full_one_eq (μ : FinDist TPolicy) {ε : ℝ} (hμ : ∀ π, 0 < μ.w π) (h0 : 0 ≤ ε)
    (h1 : ε < 1) : edtScore μ ε .full .one = 1000000 :=
  edtScore_eq_of_pos (mass_full_one_pos hμ h0 h1)

end Cleanroom.Udt.UdtPolicyCalc.Transparent
