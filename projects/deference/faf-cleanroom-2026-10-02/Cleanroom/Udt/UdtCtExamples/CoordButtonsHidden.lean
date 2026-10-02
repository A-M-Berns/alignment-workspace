import Cleanroom.Udt.UdtCtExamples.CoordButtons

/-!
# `Cleanroom.Udt.UdtCtExamples.CoordButtonsHidden`: Coordinated Buttons with the pre-choice
hidden from `Π̈` (T1, repair round 2)

Work package `udt-ct-examples`, target T1(a), added in repair round 2 (audit r1 fidelity B3 and
r2 fidelity N3/N9: the `CB W5` hidden-reading atom was hand-checked only). Source:
[[communication-trust-translated]] lines 148–158, 381–390 (decision-determination).

`CB.S W` makes the pill choice the pre-instance's external action, so `Π̈(pre) = s` reveals it
and `CB W5`'s decision-determination holds *through that leak* (findings F-2(a)): with the choice
hidden, the `Π̈`-atom `(pre ↦ $10 policy, rooms ↦ $10, $10)` contains both the pill worlds
(copy `7 : 1` towards `$10` under `wa5`) and the `$10`-policy worlds without the pill (copy
`5 : 3` towards `$5`), and clause (2) fails there. `CBh.S W` is the same 24 worlds and priors
with `Ä(pre) = k` (the agent's own room policy, the dummy `CBm` uses) and the chosen policy
`(0, k)` at every input — silent about `s`. Under `W5` decision-determination **fails** at that
atom (`not_decisionDetermined5`: `3 · 48 ≠ 10 · 24`); under `W10` it **holds**
(`decisionDetermined10`: `wa10 0 1 = wa10 1 1`). On this carrier the pill is not an action of
any instance (as on `MemH`), so `MinMod`/`IsCA` cannot be asked of it.
-/

set_option maxHeartbeats 1000000

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

namespace CBh

/-- Worlds: the same carrier as `CB` (`((s, k), (ö, a))`).
Source: none: infrastructure (repair round 2)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := CB.Ω

/-- The external action with the choice hidden: the dummy `k` at `pre`; at a room, `$10` if the
pill is active, else `k` (as `CB.actOf`).
Source: none: infrastructure (the `CBm` dummy, `Ä(pre) = k`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def actOf (s k : Fin 2) (e : Fin 3) : Fin 2 := if e = 0 then k else if s = 1 then 1 else k

/-- The utility numerator: as `CB.u` (`0` at `pre`; the room payoff otherwise).
Source: [[communication-trust-translated]] line 149
Kind: D
Fidelity: exact (scaled)
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.2.1 = 0 then 0 else CB.pay (actOf ω.1.1 ω.1.2 ω.2.1) ω.2.2

/-- Supporting lemma `u_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_le (ω : Ω) : u ω ≤ 2 := by revert ω; decide

/-- The chosen policy of dynamics `(s, k)`: `(0, k)` at every input — silent about `s`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (_s k : Fin 2) (_oe : Fin 2 × Fin 3) : Fin 1 × Fin 2 := (0, k)

/-- **Coordinated Buttons with the pre-choice hidden, abstract structure** over weights `W`.
Source: [[communication-trust-translated]] lines 148–158; mandate T1(a); audit r2 fidelity N3
Kind: N+
Fidelity: variant: the pre-choice hidden from `Π̈` (`Ä(pre) = k`, chosen policies silent about `s`); copies in law (T8′); §3 (c)
Hyps: none -/
noncomputable def absDS (W : IntWeights Ω) : AbstractDS Ω (Fin 2) (Fin 3) (Fin 1) (Fin 2) (Fin 2)
    (Fin 3 × Fin 2) (Fin 2) (Fin 1) (Fin 2) where
  μ := W.dist
  pos := W.w_pos
  oI ω := ω.1.1
  oE ω := ω.2.1
  aI _ := 0
  aE ω := actOf ω.1.1 ω.1.2 ω.2.1
  dI ω := ω.1.1
  dE ω := ω.2
  dB ω := ω.1.2
  oH _ := 0
  oC ω := ω.1.1
  polS ω := polOf' ω.1.1 ω.1.2
  U := natDiv u 2
  U_mem := natDiv_mem u (by norm_num) u_le
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω₁ ω₂ => (ω₁.1, (ω₁.2.1, ω₂.2.2))) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => ((0, actOf ω₁.1.1 ω₁.1.2 ω₁.2.1), ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((ω₁.1.1, ω₂.1.2), ω₁.2)) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₁.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **Coordinated Buttons with the pre-choice hidden, concrete structure**: no messages; the pill
forces `$10` at the rooms (`CB.pfun`).
Source: [[communication-trust-translated]] lines 148–158; mandate T1(a)
Kind: N+
Fidelity: as `absDS`
Hyps: none -/
noncomputable def S (W : IntWeights Ω) : ConcreteDS Ω (Fin 2) (Fin 3) (Fin 1) (Fin 2) (Fin 2)
    (Fin 3 × Fin 2) (Fin 2) (Fin 1) (Fin 2) where
  toAbstractDS := absDS W
  s _ _ := none
  p := CB.pfun

variable (W : IntWeights Ω)

/-- Supporting lemma: the three decidable hypotheses of `polE_eq_of`, weight-free.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_key :
    (∀ ω : Ω, actOf ω.1.1 ω.1.2 ω.2.1 = actOf ω.1.1 ω.1.2 ω.2.1) ∧
    (∀ ω ω' : Ω, (ω.1.1, ω.1.2) = (ω'.1.1, ω'.1.2) →
      (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf ω'.1.1 ω'.1.2 e) ∧
    (∀ (ω : Ω) (e : Fin 3), ∃ ω' : Ω, (ω'.1.1, ω'.1.2) = (ω.1.1, ω.1.2) ∧ ω'.2.1 = e) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`Π̈` on `CBh`**: `(pre ↦ k, rooms ↦ $10 if the pill is active else k)` — silent about the
choice when `k = $10`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : (S W).polE ω = fun e => actOf ω.1.1 ω.1.2 e :=
  (S W).polE_eq_of (fun ω e => actOf ω.1.1 ω.1.2 e) polE_key.1 polE_key.2.1 polE_key.2.2 ω

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 3 → Fin 2) :
    (S W).evPolE π = event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 2 × Fin 2) : (S W).polOf d = fun e => actOf d.1 d.2 e := by
  obtain ⟨d1, d2⟩ := d
  exact polE_eq W ((d1, d2), (0, 0))

/-- **The hidden-choice atom**: the pill dynamics and the `$10`-policy dynamics without the pill
share the external policy `(pre ↦ $10, rooms ↦ $10, $10)`.
Source: findings F-2(a)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_atom : (S W).polOf (1, 1) = (S W).polOf (0, 1) := by
  rw [polOf_eq, polOf_eq]
  funext e
  revert e
  decide

/-- **The prose meaning of `Π*` holds on `CBh`** (`hlink`).
Source: mandate T7(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hlink : ∀ ω, (S W).P ω ((S W).oE ω) = none →
    (S W).polD ω ((S W).O ω) = (S W).polS ω ((S W).O ω) := by
  intro ω h
  have h' : CB.pfun ω.2.1 ω.1.1 = none := h
  clear h
  rw [AbstractDS.polD_apply_O]
  show ((0 : Fin 1), actOf ω.1.1 ω.1.2 ω.2.1) = polOf' ω.1.1 ω.1.2 (ω.1.1, ω.2.1)
  revert ω
  decide +kernel

/-! ### Decision-determination: fails under `W5`, holds under `W10` -/

/-- Supporting lemma: `U` is a function of `E`, weight-free.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω, (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = (actOf ω'.1.1 ω'.1.2 ω'.2.1, ω'.2) →
    u ω = u ω' := by decide +kernel

/-- **Clause (1) of decision-determination on `CBh`**: `U ⊑ E`, for every prior.
Source: mandate T1(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem U_sub_E : IsSubvariable (S W).E (S W).U := by
  intro ω ω' h
  show natDiv u 2 ω = natDiv u 2 ω'
  unfold natDiv
  rw [u_of_E ω ω' h]

/-- Supporting lemma: clause (2) from a count identity over the coordinates (as `CB.dd2_of_cnt`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dd2_of_cnt
    (key : ∀ (e : Fin 2 × (Fin 3 × Fin 2)) (d : Fin 2 × Fin 2),
      W.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = e ∧ (ω.1.1, ω.1.2) = d) *
          W.cnt (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e) =
        W.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = e ∧
            (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e) *
          W.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = d)) :
    ∀ (e : Fin 2 × (Fin 3 × Fin 2)) (d : Fin 2 × Fin 2),
      mass (S W).μ.w (event fun ω => (S W).E ω = e ∧ (S W).DIB ω = d) *
          mass (S W).μ.w ((S W).evPolE ((S W).polOf d)) =
        mass (S W).μ.w (event fun ω => (S W).E ω = e ∧ (S W).polE ω = (S W).polOf d) *
          mass (S W).μ.w ((S W).evDIB d) := by
  intro e d
  have hev : (event fun ω => (S W).E ω = e ∧ (S W).polE ω = (S W).polOf d) =
      event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = e ∧
        (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e :=
    event_congr fun ω => by rw [polE_eq, polOf_eq]; rfl
  rw [hev, evPolE_eq, polOf_eq]
  exact W.mass_mul_eq_of_cnt (key e d)

/-- **`CBh.S W10` is decision-determined**: with the choice hidden, the atom
`(pre ↦ $10, rooms ↦ $10, $10)` mixes the pill worlds and the `$10`-policy worlds, whose copy
laws agree under `W10` (`wa10 0 1 = wa10 1 1`), so clause (2) survives.
Source: mandate T1(a); findings F-2(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined10 : (S CB.W10).DecisionDetermined :=
  ⟨U_sub_E CB.W10, dd2_of_cnt CB.W10 (by decide +kernel)⟩

/-- Supporting lemma: the four counts of the failing atom under `W5`, in weight units (total
`192`): `P(E = e, D_{I,B} = d) = 3`, `P(Π̈ = [[d]]) = 48`, `P(E = e, Π̈ = [[d]]) = 10`,
`P(D_{I,B} = d) = 24` at `e = ($10, (red, copy $10))`, `d = (nothing, $10 policy)`.
Source: none: infrastructure (the atom hand-checked in audit r1 fidelity B3 / r2 fidelity N3)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem key_values5 :
    CB.W5.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = (1, (1, 1)) ∧
        (ω.1.1, ω.1.2) = (0, 1)) = 3 ∧
    CB.W5.cnt (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 0 1 e) = 48 ∧
    CB.W5.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = (1, (1, 1)) ∧
        (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 0 1 e) = 10 ∧
    CB.W5.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = (0, 1)) = 24 := by
  decide +kernel

/-- Supporting lemma: the failing atom as a count inequality (`3 · 48 ≠ 10 · 24`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem key5 :
    CB.W5.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = (1, (1, 1)) ∧
        (ω.1.1, ω.1.2) = (0, 1)) *
      CB.W5.cnt (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 0 1 e) ≠
    CB.W5.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = (1, (1, 1)) ∧
        (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 0 1 e) *
      CB.W5.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = (0, 1)) := by
  decide +kernel

/-- **With the pre-choice hidden, `CB W5` is not decision-determined**: clause (2) fails at
`e = ($10, (red, copy $10))`, `d = (nothing, $10 policy)`, where the division-free identity reads
`3 · 48 = 10 · 24` (`key_values5`): inside the atom `(pre ↦ $10, rooms ↦ $10, $10)` the copy
presses `$10` with probability `7/8` in the pill worlds and `3/8` in the `$10`-policy worlds, and
`Π̈` cannot tell them apart. This is the hand-checked claim of findings F-2(a), `W5`'s docstring
and the `CB.decisionDetermined5` row, now in Lean: `CB W5`'s decision-determination holds only
through the `Π̈(pre)` leak.
Source: [[communication-trust-translated]] lines 381–390; findings F-2(a); audit r1 fidelity B3, r2 fidelity N3/N9
Kind: N+
Fidelity: exact (on this representation; the atom is named)
Hyps: none; §3 (c) -/
theorem not_decisionDetermined5 : ¬ (S CB.W5).DecisionDetermined := fun h => by
  have := h.2 (1, (1, 1)) (0, 1)
  have hev : (event fun ω => (S CB.W5).E ω = (1, (1, 1)) ∧ (S CB.W5).polE ω = (S CB.W5).polOf (0, 1)) =
      event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = (1, (1, 1)) ∧
        (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 0 1 e :=
    event_congr fun ω => by rw [polE_eq, polOf_eq]; rfl
  rw [hev, evPolE_eq, polOf_eq] at this
  apply key5
  have := congrArg (fun x => x * (CB.W5.N : ℝ) * CB.W5.N) this
  simp only [show (S CB.W5).μ.w = CB.W5.w from rfl, CB.W5.mass_eq_cnt] at this
  have hN : (CB.W5.N : ℝ) ≠ 0 := by exact_mod_cast CB.W5.N_pos.ne'
  field_simp at this
  exact_mod_cast this

end CBh

end Cleanroom.Udt.UdtCtExamples
