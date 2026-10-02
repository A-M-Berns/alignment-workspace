import Cleanroom.Udt.UdtCommTrust.SelfTrust
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCtExamples.CoordButtons

/-!
# `Cleanroom.Udt.UdtCtExamples.CoordButtonsMsg`: Coordinated Buttons with the message channel
(T1(d) — the release valve)

Work package `udt-ct-examples`, target T1(d). Source: [[communication-trust-translated]] lines
167–170 ("before being copied … you can think to yourself 'I should press the `$10` button' …
This allows communication to act as a release valve"), [[examples-revisited]] Example 1
("Communication … acts as the equilibrium-selection device").

## Why a second carrier

On `CB` the pre-instance's choice is its external action, so `Π̈(pre)` reveals it and the
communicative-alternative identity (`IsCA`: the law of the whole `Π̈` given the pill equals the
law given the message and `Π̈ = R`) cannot hold between two distinct pre-actions (report §0.1,
findings F-1). Here the choice is the pre-instance's **internal** action `c'` (`AI = Fin 2`:
`0` take the pill, `1` send the message), realized (`Ȧ(pre) = c'`), and the channel state
`s : Fin 3` (`0` neutral, `1` pill active, `2` message sent) is a separate coordinate of `D_I`,
support-independent of `c'` as `I_fac` demands and tied to it in law (`6 : 1 : 1`: the choice
takes effect with probability `3/4`). This is the paper's own picture of self-modification — "there
is merely some probabilistic relationship between internal actions and (potentially self-modifying)
internal observations" — and its price is that the pill is modifying with probability `3/4`, not
`1`, and the message with probability `1/8`. On this carrier the self-modification is modelled as
forcing only and never changes what the chosen policy would do: the chosen policy presses `$10`
on an active channel, so `Π† = Π*` at every world (audit r1 N2, r2 fidelity N8) — unlike `CB`,
where the pill overrides a `$5` press at the `(pill, $5)` worlds (`CB.pill_overrides_five`).

Worlds `(((c', s), k), (ö, a))`, 48 of them: `k : Fin 2` the room policy (`$5`/`$10`), `ö : Fin 2`
the focal instance (`pre`, red), `a : Fin 2` the copy's action (free, coupled `3 : 1` to the
agent's own action at red). Two instances only: the green room enters as the free coordinate.
`Ä = k` at `pre` (a dummy that `E_fac`/`A_fac` force to vary; it is what keeps `Π̈(pre)` silent
about `c'`); at red `$10` if the channel is active (the pill forces it; the message is followed),
else `k`. The chosen room policy follows the message and presses `k` otherwise, so
`P(Π̈ = R) = 1` **non-vacuously** (the message is sent in a third of the dynamics). Utility at red as
in `CB`.

Prior `W5m`: the choice takes effect `6 : 1 : 1`; room policies `3 : 1` towards `$5`; the copy
`3 : 1` towards the agent's own red action; pre dummy uniform. Total `768`.
-/

set_option maxHeartbeats 1000000

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

namespace CBm

/-- Worlds `(((c', s), k), (ö, a))`.
Source: none: infrastructure (mandate T1(d))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := ((Fin 2 × Fin 3) × Fin 2) × (Fin 2 × Fin 2)

/-- The external action of channel state `s` and room policy `k` at instance `e`: `k` at `pre`;
`$10` at red when the channel is active, else `k`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def actOf (s : Fin 3) (k : Fin 2) (e : Fin 2) : Fin 2 := if e = 0 then k else if s = 0 then k else 1

/-- The utility numerator: `0` at `pre`, `CB.pay` of the red action against the copy's.
Source: [[communication-trust-translated]] line 149
Kind: D
Fidelity: exact (scaled)
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.2.1 = 0 then 0 else CB.pay (actOf ω.1.1.2 ω.1.2 1) ω.2.2

/-- Supporting lemma `u_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_le (ω : Ω) : u ω ≤ 2 := by revert ω; decide

/-- The chosen policy of dynamics `(c', s, k)`: `(c', k)` at `pre`; at red, `$10` when the
internal observation shows an active channel, else `k`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (c' : Fin 2) (_s : Fin 3) (k : Fin 2) (oe : Fin 3 × Fin 2) : Fin 2 × Fin 2 :=
  if oe.2 = 0 then (c', k) else (0, if oe.1 = 0 then k else 1)

/-- The message semantics: at red, channel value `2` recommends `$10`.
Source: [[communication-trust-translated]] line 167
Kind: D
Fidelity: exact
Hyps: n/a -/
def sfun (e : Fin 2) (h : Fin 3) : Option (Fin 2) := if e = 1 ∧ h = 2 then some 1 else none

/-- The side-channel impact: at red, channel value `1` forces `$10`.
Source: [[communication-trust-translated]] line 150
Kind: D
Fidelity: exact
Hyps: n/a -/
def pfun (e : Fin 2) (c : Fin 3) : Option (Fin 2) := if e = 1 ∧ c = 1 then some 1 else none

/-- **Coordinated Buttons with the message channel, abstract structure** over weights `W`.
Source: [[communication-trust-translated]] lines 148–170; mandate T1(d)
Kind: N+
Fidelity: variant: two instances; the choice an internal action with a probabilistic effect (module docstring); the pre-instance's external action is the dummy `Ä(pre) = k` (the agent's own room policy, which `E_fac`/`A_fac` force into the pre-action — so a pre-action here is also a whole-policy choice); copies in law (T8′); §3 (c)
Hyps: none -/
noncomputable def absDS (W : IntWeights Ω) : AbstractDS Ω (Fin 3) (Fin 2) (Fin 2) (Fin 2) (Fin 3)
    (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Fin 3) (Fin 3) where
  μ := W.dist
  pos := W.w_pos
  oI ω := ω.1.1.2
  oE ω := ω.2.1
  aI ω := if ω.2.1 = 0 then ω.1.1.1 else 0
  aE ω := actOf ω.1.1.2 ω.1.2 ω.2.1
  dI ω := ω.1.1.2
  dE ω := ω.2
  dB ω := (ω.1.1.1, ω.1.2)
  oH ω := ω.1.1.2
  oC ω := ω.1.1.2
  polS ω := polOf' ω.1.1.1 ω.1.1.2 ω.1.2
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
  I_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => (((if ω₁.2.1 = 0 then ω₁.1.1.1 else 0, ω₂.1.1.2), ω₁.1.2), (0, 0)))
    (by decide +kernel)
  E_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => (((ω₁.1.1.1, 0), actOf ω₁.1.1.2 ω₁.1.2 ω₁.2.1), ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => (((ω₂.1.1.1, ω₁.1.1.2), ω₂.1.2), ω₁.2))
    (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₁.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  A_fac := factorsAs_of_fun
    (fun ω₁ ω₂ => (((if ω₁.2.1 = 0 then ω₁.1.1.1 else 0, 0), actOf ω₂.1.1.2 ω₂.1.2 ω₂.2.1),
      (0, 0))) (by decide +kernel)

/-- **Coordinated Buttons with the message channel, concrete structure.**
Source: [[communication-trust-translated]] lines 148–170; mandate T1(d)
Kind: N+
Fidelity: as `absDS`
Hyps: none -/
noncomputable def S (W : IntWeights Ω) : ConcreteDS Ω (Fin 3) (Fin 2) (Fin 2) (Fin 2) (Fin 3)
    (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Fin 3) (Fin 3) where
  toAbstractDS := absDS W
  s := sfun
  p := pfun

variable (W : IntWeights Ω)

/-- Supporting lemma: the hypotheses of `polE_eq_of`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_key :
    (∀ ω : Ω, actOf ω.1.1.2 ω.1.2 ω.2.1 = actOf ω.1.1.2 ω.1.2 ω.2.1) ∧
    (∀ ω ω' : Ω, (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (ω'.1.1.2, (ω'.1.1.1, ω'.1.2)) →
      (fun e => actOf ω.1.1.2 ω.1.2 e) = fun e => actOf ω'.1.1.2 ω'.1.2 e) ∧
    (∀ (ω : Ω) (e : Fin 2), ∃ ω' : Ω,
      (ω'.1.1.2, (ω'.1.1.1, ω'.1.2)) = (ω.1.1.2, (ω.1.1.1, ω.1.2)) ∧ ω'.2.1 = e) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`Π̈` on `CBm`.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : (S W).polE ω = fun e => actOf ω.1.1.2 ω.1.2 e :=
  (S W).polE_eq_of (fun ω e => actOf ω.1.1.2 ω.1.2 e) polE_key.1 polE_key.2.1 polE_key.2.2 ω

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 2 → Fin 2) :
    (S W).evPolE π = event fun ω : Ω => (fun e => actOf ω.1.1.2 ω.1.2 e) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 3 × (Fin 2 × Fin 2)) : (S W).polOf d = fun e => actOf d.1 d.2.2 e := by
  obtain ⟨d1, d2, d3⟩ := d
  exact polE_eq W (((d2, d1), d3), (0, 0))

/-- Supporting lemma `evS_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_eq (o : Fin 3) (e : Fin 2) (a : Fin 2 × Fin 2) :
    (S W).evS o e a = event fun ω : Ω => polOf' ω.1.1.1 ω.1.1.2 ω.1.2 (o, e) = a := rfl

/-- **`Π* ⊑ D_{I,B}` on `CBm`.**
Source: mandate T1(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem polS_sub : IsSubvariable (S W).DIB (S W).polS := by
  show ∀ ω ω' : Ω, (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (ω'.1.1.2, (ω'.1.1.1, ω'.1.2)) →
    polOf' ω.1.1.1 ω.1.1.2 ω.1.2 = polOf' ω'.1.1.1 ω'.1.1.2 ω'.1.2
  decide +kernel

/-- **`R ⊑ D_{I,B}` on `CBm`.**
Source: mandate T1(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem R_sub_DIB : IsSubvariable (S W).DIB (S W).R := by
  show ∀ ω ω' : Ω, (ω.1.1.2, (ω.1.1.1, ω.1.2)) = (ω'.1.1.2, (ω'.1.1.1, ω'.1.2)) →
    (fun e => sfun e ω.1.1.2) = fun e => sfun e ω'.1.1.2
  decide +kernel

/-- **`P(Π̈ = R) = 1` on `CBm`, non-vacuously**: the message is sent in a third of the dynamics
and every chosen room policy follows it.
Source: mandate T1(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem followsR : mass (S W).μ.w (S W).evFollowsR = 1 := by
  have : (S W).evFollowsR = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ω
    rw [ConcreteDS.mem_evFollowsR, polE_eq]
    show ConcreteDS.Follows (fun e => actOf ω.1.1.2 ω.1.2 e) (fun e => sfun e ω.1.1.2)
    revert ω
    decide +kernel
  rw [this]
  exact mass_univ (S W).μ

/-- Supporting lemma `evMod_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evMod_eq : (S W).evMod = event fun ω : Ω => ω.1.1.2 = 1 := by
  ext ω
  simp only [ConcreteDS.evMod, mem_event]
  show (∃ e : Fin 2, (pfun e ω.1.1.2).isSome) ↔ ω.1.1.2 = 1
  revert ω
  decide +kernel

/-- Supporting lemma: attainment at the pre input (all four actions).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_pre_nonempty (o : Fin 3) (a : Fin 2 × Fin 2) : ((S W).evS o 0 a).Nonempty := by
  rw [evS_eq]; revert o a; decide +kernel

/-- **The prose meaning of `Π*` holds on `CBm`** (`hlink`), including at the pre-instance,
where the realized internal action is the chosen one.
Source: mandate T1(d), T7(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hlink : ∀ ω, (S W).P ω ((S W).oE ω) = none →
    (S W).polD ω ((S W).O ω) = (S W).polS ω ((S W).O ω) := by
  intro ω h
  have h' : pfun ω.2.1 ω.1.1.2 = none := h
  clear h
  rw [AbstractDS.polD_apply_O]
  show ((if ω.2.1 = 0 then ω.1.1.1 else 0), actOf ω.1.1.2 ω.1.2 ω.2.1) =
    polOf' ω.1.1.1 ω.1.1.2 ω.1.2 (ω.1.1.2, ω.2.1)
  revert ω
  decide +kernel

/-! ### The prior and decision-determination -/

/-- The prior `W5m` (module docstring).
Source: mandate T1(d)
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def W5m : IntWeights Ω where
  wt ω := (if ω.1.1.2 = Fin.succ ω.1.1.1 then 6 else 1) * (if ω.1.2 = 0 then 3 else 1) *
    (if ω.2.1 = 0 then 4 else if ω.2.2 = actOf ω.1.1.2 ω.1.2 1 then 3 else 1)
  pos ω := by revert ω; decide
  N := 768
  sum_eq := by decide +kernel

/-- Supporting lemma: `U ⊑ E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω,
    (actOf ω.1.1.2 ω.1.2 ω.2.1, ω.2) = (actOf ω'.1.1.2 ω'.1.2 ω'.2.1, ω'.2) → u ω = u ω' := by
  decide +kernel

/-- Supporting lemma: clause (2) as a count identity under `W5m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dd_key : ∀ (e : Fin 2 × (Fin 2 × Fin 2)) (d : Fin 3 × (Fin 2 × Fin 2)),
    W5m.cnt (event fun ω : Ω => (actOf ω.1.1.2 ω.1.2 ω.2.1, ω.2) = e ∧
        (ω.1.1.2, (ω.1.1.1, ω.1.2)) = d) *
      W5m.cnt (event fun ω : Ω => (fun e => actOf ω.1.1.2 ω.1.2 e) = fun e => actOf d.1 d.2.2 e) =
    W5m.cnt (event fun ω : Ω => (actOf ω.1.1.2 ω.1.2 ω.2.1, ω.2) = e ∧
        (fun e => actOf ω.1.1.2 ω.1.2 e) = fun e => actOf d.1 d.2.2 e) *
      W5m.cnt (event fun ω : Ω => (ω.1.1.2, (ω.1.1.1, ω.1.2)) = d) := by
  decide +kernel

/-- **`CBm.S W5m` is decision-determined.**
Source: mandate T1(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : (S W5m).DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · show natDiv u 2 ω = natDiv u 2 ω'
    unfold natDiv
    rw [u_of_E ω ω' h]
  · have hev : (event fun ω => (S W5m).E ω = e ∧ (S W5m).polE ω = (S W5m).polOf d) =
        event fun ω : Ω => (actOf ω.1.1.2 ω.1.2 ω.2.1, ω.2) = e ∧
          (fun e => actOf ω.1.1.2 ω.1.2 e) = fun e => actOf d.1 d.2.2 e :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]; rfl
    rw [hev, evPolE_eq, polOf_eq]
    exact W5m.mass_mul_eq_of_cnt (dd_key e d)

/-! ### Modification: the pill `3/4`, the message `1/8` -/

/-- Supporting lemma `modS_eq_cnt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem modS_le_of_cnt {o : Fin 3} {e : Fin 2} {a b : Fin 2 × Fin 2}
    (ha : ((S W).evS o e a).Nonempty) (hb : ((S W).evS o e b).Nonempty)
    (h : W.cnt ((event fun ω : Ω => ω.1.1.2 = 1) ∩ (S W).evS o e a) * W.cnt ((S W).evS o e b) ≤
      W.cnt ((event fun ω : Ω => ω.1.1.2 = 1) ∩ (S W).evS o e b) * W.cnt ((S W).evS o e a)) :
    (S W).modS o e a ≤ (S W).modS o e b := by
  unfold ConcreteDS.modS ConcreteDS.modProb
  rw [evMod_eq]
  exact condProbJunk_le_of_cnt W ha hb h

/-- **The message actions are minimally modifying at the pre input** (`m = 1/8`, against `3/4`
for the pill actions).
Source: mandate T1(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem minMod_msg (o : Fin 3) (k : Fin 2) : (S W5m).MinMod o 0 (1, k) := by
  intro a' ha'
  refine modS_le_of_cnt W5m (evS_pre_nonempty W5m o (1, k)) ha' ?_
  rw [evS_eq, evS_eq]
  revert o k a'
  decide +kernel

/-- **The pill actions are not minimally modifying at the pre input.**
Source: mandate T1(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_pill (o : Fin 3) (k : Fin 2) : ¬ (S W5m).MinMod o 0 (0, k) := by
  have h2 : (S W5m).modS o 0 (1, k) < (S W5m).modS o 0 (0, k) := by
    unfold ConcreteDS.modS ConcreteDS.modProb
    rw [evMod_eq]
    refine condProbJunk_lt_of_cnt W5m (evS_pre_nonempty W5m o (1, k))
      (evS_pre_nonempty W5m o (0, k)) ?_
    rw [evS_eq, evS_eq]
    revert o k
    decide +kernel
  intro h
  exact absurd (h (1, k) (evS_pre_nonempty W5m o (1, k))) (not_le.2 h2)

/-! ### Communicative alternatives: the message is the pill's -/

/-- **At the pre input the message action is a communicative alternative of the pill action with
the same room policy**: it is minimally modifying and the law of `Π̈` given `(pill, k)` is the
law given `(message, k)` and `Π̈ = R` — both put all their mass on the profile that presses
`$10` at red when the channel is active and `k` otherwise, with the channel active with the
same probability `7/8` under either choice.
Source: [[communication-trust-translated]] lines 167–170, 449–456; mandate T1(d) (the release valve)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem isCA_pill_msg (o : Fin 3) (k : Fin 2) : (S W5m).IsCA o 0 (0, k) (1, k) := by
  refine ⟨minMod_msg o k, forall_fun2 fun x y => ?_⟩
  rw [(ConcreteDS.evFollowsR_eq_univ_iff (S W5m)).1 (followsR W5m), Finset.inter_univ, evPolE_eq]
  exact W5m.condProbJunk_eq_of_cnt (evS_pre_nonempty W5m o (0, k)) (evS_pre_nonempty W5m o (1, k))
    (ca_key o k x y)
where
  ca_key : ∀ (o : Fin 3) (k x y : Fin 2),
      W5m.cnt ((event fun ω : Ω => (fun e => actOf ω.1.1.2 ω.1.2 e) =
            fun e => if e = 0 then x else y) ∩ (S W5m).evS o 0 (0, k)) *
          W5m.cnt ((S W5m).evS o 0 (1, k)) =
        W5m.cnt ((event fun ω : Ω => (fun e => actOf ω.1.1.2 ω.1.2 e) =
            fun e => if e = 0 then x else y) ∩ (S W5m).evS o 0 (1, k)) *
          W5m.cnt ((S W5m).evS o 0 (0, k)) := by
    simp only [evS_eq]
    decide +kernel

/-- **At a red input every attained action is minimally modifying**, so it is its own
communicative alternative under `P(Π̈ = R) = 1`.
Source: mandate T1(d)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem minMod_red (o : Fin 3) (a : Fin 2 × Fin 2) (ha : ((S W5m).evS o 1 a).Nonempty) :
    (S W5m).MinMod o 1 a := by
  intro a' ha'
  refine modS_le_of_cnt W5m ha ha' ?_
  rw [evS_eq] at ha ha' ⊢
  rw [evS_eq]
  revert o a a'
  decide +kernel

/-- **`CBm.S W5m` has communicative alternatives** (load-bearing for T1(d)): at the pre input the
message with the same room policy; at the red input every attained action itself.
Source: [[communication-trust-translated]] line 458; mandate T1(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hasCA : (S W5m).HasCA := by
  intro o e a ha
  rcases fin2_cases e with rfl | rfl
  · obtain ⟨x, k⟩ := a
    rcases fin2_cases x with rfl | rfl
    · exact ⟨(1, k), isCA_pill_msg o k⟩
    · exact ⟨(1, k), (S W5m).isCA_self_of_minMod (followsR W5m) (minMod_msg o k)⟩
  · exact ⟨a, (S W5m).isCA_self_of_minMod (followsR W5m) (minMod_red o a ha)⟩

/-! ### The repaired Self-Trust theorem applies, and its conclusion is exercised -/

/-- **The repaired Self-Trust theorem applies to `CBm.S W5m`** — every hypothesis holds,
none vacuously.
Source: mandate T1(d) ("`selfTrust_repaired` applies — the release valve")
Kind: C
Fidelity: n/a
Hyps: (a) `selfTrust_repaired`; §3 (c) -/
theorem selfTrust_applies (o : Fin 3) (e : Fin 2) :
    ∃ a, (S W5m).MinMod o e a ∧ IsArgmax ((S W5m).score o e) a :=
  (S W5m).selfTrust_repaired decisionDetermined (polS_sub W5m) (R_sub_DIB W5m) hasCA
    (followsR W5m) o e

/-- Supporting lemma `score_lt_of_cnt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem score_lt_of_cnt {o : Fin 3} {e : Fin 2} {a b : Fin 2 × Fin 2}
    (ha : ((S W).evS o e a).Nonempty) (hb : ((S W).evS o e b).Nonempty)
    (h : csum W u ((S W).evS o e a) * W.cnt ((S W).evS o e b) <
      csum W u ((S W).evS o e b) * W.cnt ((S W).evS o e a)) :
    (S W).score o e a < (S W).score o e b :=
  condExpJunk_natDiv_lt W u (by norm_num) ha hb h (-1)

/-- **The `$5`-policy actions lose strictly at the pre input** (`45/64` against `3/4`, times the
red mass): the argmax set is a proper subset of the attained actions.
Source: mandate T1(d) ("N+ for the conclusion only if the argmax set is a proper subset")
Kind: P
Fidelity: exact (computed)
Hyps: none -/
theorem score_k5_lt (o : Fin 3) (c : Fin 2) : (S W5m).score o 0 (c, 0) < (S W5m).score o 0 (c, 1) := by
  refine score_lt_of_cnt W5m (evS_pre_nonempty W5m o (c, 0)) (evS_pre_nonempty W5m o (c, 1)) ?_
  rw [evS_eq, evS_eq]
  revert o c
  decide +kernel

/-- **The pill and the message with the same room policy score the same at the pre input.**
Source: mandate T1(d) (the tie `commExp_printed` predicts)
Kind: P
Fidelity: exact (computed)
Hyps: none -/
theorem score_tie (o : Fin 3) (k : Fin 2) : (S W5m).score o 0 (0, k) = (S W5m).score o 0 (1, k) := by
  refine condExpJunk_natDiv_eq W5m u (by norm_num) (evS_pre_nonempty W5m o (0, k))
    (evS_pre_nonempty W5m o (1, k)) ?_ (-1)
  rw [evS_eq, evS_eq]
  revert o k
  decide +kernel

/-- **The message with the `$10` room policy is a minimally modifying UDT argmax at the pre
input, and the `$5`-policy actions are not argmaxes**: the conclusion of `selfTrust_repaired` is
exercised on a proper subset — communication is the release valve on this witness. Where the
properness comes from (audit r1 fidelity N1): the argmax set `{(pill, $10), (message, $10)}` is
separated from `{(pill, $5), (message, $5)}` only by the dummy coordinate `Ä(pre) = k`, the
agent's own room policy; projected onto the source's choice (pill / message) every attained
action is an argmax — the tie `score_tie` that `commExp_printed` predicts. So this is not the
three-pre-choice variant `udt-comm-trust` left open (a third *pre-choice*, not the same choice
with another room policy).
Source: [[communication-trust-translated]] lines 167–170; mandate T1(d)
Kind: N+
Fidelity: n/a (properness through the dummy coordinate; on the source's choice alone the argmax set is everything)
Hyps: none -/
theorem release_valve (o : Fin 3) :
    ((S W5m).MinMod o 0 (1, 1) ∧ IsArgmax ((S W5m).score o 0) (1, 1)) ∧
      ∀ c, ¬ IsArgmax ((S W5m).score o 0) (c, 0) := by
  refine ⟨⟨minMod_msg o 1, fun a => ?_⟩, fun c h => absurd (h (c, 1)) (not_le.2 (score_k5_lt o c))⟩
  obtain ⟨x, k⟩ := a
  rcases fin2_cases k with rfl | rfl
  · exact (score_k5_lt o x).le.trans (by rcases fin2_cases x with rfl | rfl <;> simp [score_tie])
  · rcases fin2_cases x with rfl | rfl
    · exact (score_tie o 1).le
    · exact le_rfl

end CBm

end Cleanroom.Udt.UdtCtExamples
