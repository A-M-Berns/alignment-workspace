import Cleanroom.Udt.UdtCtExamples.Memory

/-!
# `Cleanroom.Udt.UdtCtExamples.MemoryHidden`: the Memory Problem with the pill choice hidden
from `Π̈` (T2, repair round 1)

Work package `udt-ct-examples`, target T2, added in repair round 1 from the two audit-r1 probes
(`MemHidden.lean`, adversarial; `MemHiddenFid.lean`, fidelity — written independently and
reaching the same atom). Source: [[communication-trust-translated]] lines 159–166 and 176–178
(internal observations and actions, "such as recalling or storing memories"); the mandate's T2
sketch ("internal action: which pill, if any"); [[examples-revisited]] Example 2.

## Why a second Memory carrier

`Mem.S` makes the pill choice the light instance's *external* action (`Ä(light) = [d ≠ 0]`), so
`Π̈(light)` reveals whether a pill was taken, and decision-determination's clause (2)
(`E ⊥ D_{I,B} ∣ Π̈`) holds *because of that leak*: inside a `Π̈`-atom the pill content is fixed,
and the light's law (`7 : 1` towards the pill's colour) depends on the dynamics only through
it. The paper's own picture of the pill is an internal action with "merely some probabilistic
relationship" to the later internal observation — a self-modification the external policy does
not display.

`MemH.S` is the same 24 worlds `((d, r), (ö, ℓ))` with the same weights, pills and utility as
`Mem.S`; the only change is the light instance's external action, which is now the dummy `r`
(the unforced report — a coordinate `E_fac` forces `Ä(light)` to range over, exactly as `CBm`
uses `Ä(pre) = k`), and the chosen policy outputs `r` at every input. The pill choice appears
nowhere in `Π̈ = (light ↦ r, asked ↦ report)`. Every field of `AbstractDS` holds, `hlink` holds,
clause (1) of decision-determination holds — and **clause (2) fails** at the atom
`e = (report red, (asked, light red))`, `d = (red pill, r = red)`, where the count identity reads
`7 · 20 = 11 · 10` (`key_values`): given the report "red", the light is red with probability
`7/8` after a pill and `1/2` without one, while `Π̈` is the same.

So the DD-versus-CA diagnosis of the Memory Problem is decided by the representation of the pill
(findings F-15): with the choice visible in `Π̈` (`Mem`) DD holds and CA fails through the leak;
with it hidden (`MemH`) DD fails — the diagnosis [[examples-revisited]] retracted holds on the
paper's own internal-action picture, and its correction addresses clause (1) only. On `MemH` the
pill is not an action of any instance, so `IsCA`/`MinMod` cannot be asked of it (there is no
`Π*`-event "took the pill"); the natural carrier on which both questions can be asked at once
(a realized internal action `c'` correlated with `d` in law, `CBm`-style, 48 worlds) is recorded
as open — see `udt-ct-examples-open.txt`.
-/

set_option maxHeartbeats 1000000

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

namespace MemH

/-- Worlds: the same carrier as `Mem` (`((d, r), (ö, ℓ))`).
Source: none: infrastructure (mandate T2; repair round 1)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Mem.Ω

/-- The external action with the pill choice hidden: the dummy `r` at a light instance; the
report at the asked instance (forced by the pill when `d ≠ 0`, else `r`) — as in `Mem.actOf`.
Source: none: infrastructure (the mandate's T2 sketch: the pill is an internal matter)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def actOf (d : Fin 3) (r : Fin 2) (e : Fin 3) : Fin 2 :=
  if e = 2 then (if d = 0 then r else if d = 1 then 0 else 1) else r

/-- The chosen policy outputs `r` at every input; the pill choice is not an action of any
instance.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (_d : Fin 3) (r : Fin 2) (_oe : Fin 3 × Fin 3) : Fin 1 × Fin 2 := (0, r)

/-- The utility numerator: `1` iff the focal instance is asked and the report equals the light
(the same function as `Mem.u`, since the report is the same function of `(d, r)` and `U = 0` at
the light instances).
Source: [[communication-trust-translated]] line 160 ("rewarded for a correct answer")
Kind: D
Fidelity: exact
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.2.1 = 1 ∧ actOf ω.1.1 ω.1.2 (Mem.obs ω) = ω.2.2 then 1 else 0

/-- Supporting lemma `u_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_le (ω : Ω) : u ω ≤ 1 := by revert ω; decide

/-- **The hidden-pill Memory Problem as an abstract decision structure**: `Mem.S`'s worlds,
weights (`Mem.weights`), pills and utility, with the pill choice absent from every action.
Source: [[communication-trust-translated]] lines 159–166, 176–178; mandate T2 (the sketch's internal pill); audit r1 probes `MemHidden`, `MemHiddenFid`
Kind: N+
Fidelity: variant: the pill choice is hidden from `Π̈` (module docstring); `Ä(light)` the dummy `r`; pill content and light correlated in law only; §3 (c)
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 3) (Fin 3) (Fin 1) (Fin 2) (Fin 3) (Fin 2 × Fin 2)
    (Fin 2) (Fin 1) (Fin 3) where
  μ := Mem.weights.dist
  pos := Mem.weights.w_pos
  oI ω := ω.1.1
  oE := Mem.obs
  aI _ := 0
  aE ω := actOf ω.1.1 ω.1.2 (Mem.obs ω)
  dI ω := ω.1.1
  dE ω := ω.2
  dB ω := ω.1.2
  oH _ := 0
  oC ω := ω.1.1
  polS ω := polOf' ω.1.1 ω.1.2
  U := natDiv u 1
  U_mem := natDiv_mem u (by norm_num) u_le
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => ((0, actOf ω₁.1.1 ω₁.1.2 (Mem.obs ω₁)), ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((ω₁.1.1, ω₂.1.2), ω₁.2)) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₁.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **The hidden-pill Memory Problem as a concrete decision structure**: no messages, the pills
force the report (as `Mem.S`).
Source: [[communication-trust-translated]] lines 159–166; mandate T2
Kind: N+
Fidelity: as `absDS`
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 3) (Fin 3) (Fin 1) (Fin 2) (Fin 3) (Fin 2 × Fin 2)
    (Fin 2) (Fin 1) (Fin 3) where
  toAbstractDS := absDS
  s _ _ := none
  p := Mem.pfun

/-- **`Π̈` on `MemH`**: `(light ↦ r, asked ↦ report)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun e => actOf ω.1.1 ω.1.2 e :=
  S.polE_eq_of (fun ω e => actOf ω.1.1 ω.1.2 e) (fun _ => rfl) (by decide +kernel)
    (by decide +kernel) ω

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 3 × Fin 2) : S.polOf d = fun e => actOf d.1 d.2 e := by
  obtain ⟨d1, d2⟩ := d
  exact polE_eq ((d1, d2), (0, 0))

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 3 → Fin 2) :
    S.evPolE π = event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- **The chosen policy is blind to the pill**: `Π*` depends on `(d, r)` through `r` only.
Source: mandate T2 (the sketch's internal pill)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polS_hides_pill (ω ω' : Ω) (h : ω.1.2 = ω'.1.2) : S.polS ω = S.polS ω' := by
  show polOf' ω.1.1 ω.1.2 = polOf' ω'.1.1 ω'.1.2
  unfold polOf'; rw [h]

/-- **The prose meaning of `Π*` holds on `MemH`** (`hlink`): at every unforced realized input the
effective action is the chosen one.
Source: mandate T7(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω) := by
  intro ω h
  have h' : Mem.pfun (Mem.obs ω) ω.1.1 = none := h
  clear h
  rw [AbstractDS.polD_apply_O]
  show ((0 : Fin 1), actOf ω.1.1 ω.1.2 (Mem.obs ω)) = polOf' ω.1.1 ω.1.2 (ω.1.1, Mem.obs ω)
  revert ω
  decide +kernel

/-- Supporting lemma: `U` is a function of `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω,
    (actOf ω.1.1 ω.1.2 (Mem.obs ω), ω.2) = (actOf ω'.1.1 ω'.1.2 (Mem.obs ω'), ω'.2) →
    u ω = u ω' := by decide +kernel

/-- **Clause (1) of decision-determination holds on `MemH`**: `U ⊑ E` — the clause
[[examples-revisited]]'s correction argues ("the reward depends only on the external report and
the actual light color"), which both representations satisfy.
Source: [[examples-revisited]] Example 2 (corrected); mandate T2(a)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem U_sub_E : IsSubvariable S.E S.U := by
  intro ω ω' h
  show natDiv u 1 ω = natDiv u 1 ω'
  unfold natDiv
  rw [u_of_E ω ω' h]

/-- Supporting lemma: the four counts of the failing atom, in weight units (total `60`):
`P(E = e, D_{I,B} = d) = 7`, `P(Π̈ = [[d]]) = 20`, `P(E = e, Π̈ = [[d]]) = 11`, `P(D_{I,B} = d) = 10`
at `e = (report red, (asked, light red))`, `d = (red pill, r = red)`.
Source: none: infrastructure (audit r1 probe `MemHidden.key_values`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem key_values :
    Mem.weights.cnt (event fun ω : Ω =>
        (actOf ω.1.1 ω.1.2 (Mem.obs ω), ω.2) = (0, (1, 0)) ∧ (ω.1.1, ω.1.2) = (1, 0)) = 7 ∧
    Mem.weights.cnt (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 1 0 e) = 20 ∧
    Mem.weights.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 (Mem.obs ω), ω.2) = (0, (1, 0)) ∧
        (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 1 0 e) = 11 ∧
    Mem.weights.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = (1, 0)) = 10 := by decide +kernel

/-- Supporting lemma: the failing atom as a count inequality (`7 · 20 ≠ 11 · 10`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem key :
    Mem.weights.cnt (event fun ω : Ω =>
        (actOf ω.1.1 ω.1.2 (Mem.obs ω), ω.2) = (0, (1, 0)) ∧ (ω.1.1, ω.1.2) = (1, 0)) *
      Mem.weights.cnt (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 1 0 e) ≠
    Mem.weights.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 (Mem.obs ω), ω.2) = (0, (1, 0)) ∧
        (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 1 0 e) *
      Mem.weights.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = (1, 0)) := by decide +kernel

/-- **With the pill choice hidden from `Π̈`, the Memory Problem is not decision-determined**:
clause (2) fails at `e = (report red, (asked, light red))`, `d = (red pill, r = red)`, where the
division-free identity reads `7 · 20 = 11 · 10` (`key_values`). Given the report "red", the light
is red with probability `7/8` after a pill and `1/2` without one, and `Π̈ = (red, red, red)` either
way. This is the diagnosis [[examples-revisited]] retracted on 2026-08-05, holding on the paper's
own internal-action picture of the pill; `Mem.decisionDetermined` holds on the other
representation because `Π̈(light)` carries the choice (findings F-15).
Source: [[examples-revisited]] Example 2 (the retracted diagnosis); [[communication-trust-translated]] lines 159–166, 176–178, 381–390; mandate T2(a) ("record the atom")
Kind: N+
Fidelity: exact (on this representation; the atom is named)
Hyps: none; §3 (c) -/
theorem not_decisionDetermined : ¬ S.DecisionDetermined := fun h => by
  have := h.2 (0, (1, 0)) (1, 0)
  have hev : (event fun ω => S.E ω = (0, (1, 0)) ∧ S.polE ω = S.polOf (1, 0)) =
      event fun ω : Ω => (actOf ω.1.1 ω.1.2 (Mem.obs ω), ω.2) = (0, (1, 0)) ∧
        (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 1 0 e :=
    event_congr fun ω => by rw [polE_eq, polOf_eq]; rfl
  rw [hev, evPolE_eq, polOf_eq] at this
  apply key
  have := congrArg (fun x => x * (Mem.weights.N : ℝ) * Mem.weights.N) this
  simp only [show S.μ.w = Mem.weights.w from rfl, Mem.weights.mass_eq_cnt] at this
  have hN : (Mem.weights.N : ℝ) ≠ 0 := by exact_mod_cast Mem.weights.N_pos.ne'
  field_simp at this
  exact_mod_cast this

end MemH

end Cleanroom.Udt.UdtCtExamples
