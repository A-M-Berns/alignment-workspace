import Cleanroom.Udt.UdtCtExamples.MemoryInternal

/-!
# Audit r3 (adversarial) probe: `MemI`'s report-coordinate separation is conditional on the
dummy `r`

`MemI.report_law_differs` compares `P(Π̈(asked) = r ∣ Π*(ȯ, ö) = (pill, r))` with
`P(Π̈(asked) = r ∣ Π*(ȯ, ö) = (nothing, r))` — the action at a light input is `(c', r)` because
the light instance's external action is the dummy `r` (the unforced report policy), which
`E_fac` forces to be two-valued. So the conditioning fixes `r`. This probe asks what the report's
law looks like when the pill action alone is conditioned on (`{c' = 1}`, the union of the two
`evS o e (1, r)` at any light input, against `{c' = 0}`): it is the same fair coin either way
(`report_marginal_agrees`, both `128 / 256 = 1/2`) — the counterpart of `Mem.asked_law_agrees`,
on the carrier the package calls the paper's own picture. The joint law of `Π̈ = (r, r, report)`
does differ (`joint_differs`), but only because `Π̈(light) = r` carries the dummy: the
separation lives in the dummy's coordinate. Evidence only; not library code.
-/

namespace Cleanroom.Udt.UdtCtExamples.AuditR3.MemIMarginal

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset MemI

/-- The pill worlds, the report policy not fixed. -/
abbrev pill : Finset MemI.Ω := event fun ω : MemI.Ω => ω.1.1.1 = 1

/-- The "nothing" worlds, the report policy not fixed. -/
abbrev nothing : Finset MemI.Ω := event fun ω : MemI.Ω => ω.1.1.1 = 0

theorem pill_nonempty : pill.Nonempty := ⟨(((1, 0), 0), (0, 0)), mem_event.2 rfl⟩

theorem nothing_nonempty : nothing.Nonempty := ⟨(((0, 0), 0), (0, 0)), mem_event.2 rfl⟩

/-- `{c' = 1}` is the union over `r` of the pill actions' events at every light input. -/
theorem pill_eq_union : ∀ (o e : Fin 3), e ≠ 2 → ∀ ω : MemI.Ω,
    ω ∈ pill ↔ ω ∈ S.evS o e (1, 0) ∪ S.evS o e (1, 1) := by
  simp only [evS_eq, mem_union, mem_event]
  decide +kernel

/-- The report's law is the same under the pill and under "nothing" once `r` is averaged:
`128 · 256 = 128 · 256` for each report value. -/
theorem key : ∀ x : Fin 2,
    weights.cnt ((event fun ω : MemI.Ω => MemH.actOf ω.1.1.2 ω.1.2 2 = x) ∩ pill) *
        weights.cnt nothing =
      weights.cnt ((event fun ω : MemI.Ω => MemH.actOf ω.1.1.2 ω.1.2 2 = x) ∩ nothing) *
        weights.cnt pill := by
  decide +kernel

theorem values :
    weights.cnt pill = 256 ∧ weights.cnt nothing = 256 ∧
    weights.cnt ((event fun ω : MemI.Ω => MemH.actOf ω.1.1.2 ω.1.2 2 = 0) ∩ pill) = 128 ∧
    weights.cnt ((event fun ω : MemI.Ω => MemH.actOf ω.1.1.2 ω.1.2 2 = 0) ∩ nothing) = 128 := by
  decide +kernel

/-- **On `MemI.S` the report's marginal law is the same fair coin given the pill and given
"nothing"** (the report policy not fixed): `P(Π̈(asked) = x ∣ c' = 1) = P(Π̈(asked) = x ∣ c' = 0)`. -/
theorem report_marginal_agrees (x : Fin 2) :
    condProbJunk S.μ.w (event fun ω : MemI.Ω => S.polE ω 2 = x) pill 0 =
      condProbJunk S.μ.w (event fun ω : MemI.Ω => S.polE ω 2 = x) nothing 0 := by
  have h1 : (event fun ω : MemI.Ω => S.polE ω 2 = x) =
      event fun ω : MemI.Ω => MemH.actOf ω.1.1.2 ω.1.2 2 = x :=
    event_congr fun ω => by rw [polE_eq]
  rw [h1, show S.μ.w = weights.w from rfl]
  exact weights.condProbJunk_eq_of_cnt pill_nonempty nothing_nonempty (key x)

/-- The joint law of `Π̈ = (r, r, report)` does differ between `{c' = 1}` and `{c' = 0}` at the
profile `(0, 0, 0)`: `40 · 256 ≠ 56 · 256` — the separation is carried by the dummy coordinate
`Π̈(light) = r` jointly with the report, not by the report alone. -/
theorem joint_differs :
    weights.cnt ((event fun ω : MemI.Ω => (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun _ => 0) ∩
        pill) * weights.cnt nothing ≠
      weights.cnt ((event fun ω : MemI.Ω => (fun e => MemH.actOf ω.1.1.2 ω.1.2 e) = fun _ => 0) ∩
        nothing) * weights.cnt pill := by
  decide +kernel

end Cleanroom.Udt.UdtCtExamples.AuditR3.MemIMarginal
