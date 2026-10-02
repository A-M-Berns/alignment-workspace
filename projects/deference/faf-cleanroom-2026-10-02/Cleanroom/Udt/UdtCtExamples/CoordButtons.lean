import Cleanroom.Udt.UdtCommTrust.Advice
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCtExamples.CountExt

/-!
# `Cleanroom.Udt.UdtCtExamples.CoordButtons`: the Coordinated Buttons problem (T1)

Work package `udt-ct-examples`, target T1. Source: [[communication-trust-translated]] lines
148–158 (the example, its footnote "if you expect that's what you'll end up doing, then it is in
fact what you end up doing"), [[examples-revisited]] Example 1 (corrected 2026-08-05).

## The structure `CB.S W`

Worlds `((s, k), (ö, a))`, 24 of them:
* `s : Fin 2` — the channel state, `0` neutral, `1` the pill is active. It is the internal dynamic
  `D_I`, the internal observation `Ȯ` and the side channel `Ǒ` at every instance; at the rooms the
  side-channel impact `p` forces `$10` when `s = 1`.
* `k : Fin 2` — the chosen room policy, `0` press `$5`, `1` press `$10`; the boundary dynamic `D_B`.
* `ö : Fin 3` — the focal instance: `0` the pre-copy self, `1` the red room, `2` the green room.
* `a : Fin 2` — the *other* room's action, a free environment coordinate (`D_E = (ö, a)`), tied to
  the agent's external policy at the other room only through the prior's weights (mandate §3,
  `udt-comm-trust` finding T8′: a functional copy is not representable, so "functional identity"
  is a belief — ATTRIBUTION-UNVETTED that the paper intends otherwise). At `ö = pre` it is a dummy.

External action `Ä = actOf s k ö`: at a room, `$10` if the pill is active, else `k`; **at `pre`,
`Ä = s` — the pill choice is the pre-instance's external action.** This is the package's second
modelling substitution `(c)`, forced by the abstract structure: an internal action `Ȧ(pre)` is
support-independent of every subvariable of `D_I` (`aI_indep_of_dI`, from `I_fac`), and the
rooms' side channel sits in `D_I` (`Ǒ ⊑ Ȯ ⊑ (Ȧ, D_I)` with `Ȧ` constant at the rooms), so no
internal action at `pre` can determine it. The paper's own remark that "there is merely some
probabilistic relationship between internal actions and (potentially self-modifying) internal
observations" (C&T LaTeX draft, Modification) is what the structure enforces; rendering the
choice as `Ä(pre)` keeps it deterministic (`m(pill) = 1`, `m(nothing) = 0`) and keeps the prose
meaning of `Π*` (`Π† = Π*` at every unforced realized input, `hlink`) at the cost that `Π̈(pre)`
reveals the choice. Nothing in `E` reads it: `U = 0` at `pre` (the mandate's "else `0`" option;
the pill comparison is made at the `pre` input through the room worlds sharing its dynamics).
Utility at a room: `1/2` if both press `$5`, `1` if both `$10`, else `0` (`u / 2`).

`AI = Fin 1` (no internal action is realized); `OH = Fin 1` (no message in this structure —
the message channel is `CBm`, `CoordButtonsMsg.lean`); `Π*(ω)(ȯ, ö') = (0, s)` at `ö' = pre` and
`(0, k)` at a room: the chosen policy presses its default `k` at the rooms whatever it observes,
and chooses the channel state at `pre`.

## Priors

`W5` (the `$5`-concentrated prior): the copy's action is believed to be `$5` with weight `7 : 1`
when the agent's own room policy is `$5`, `5 : 3` when it is `$10` (the prior "expects `$5`"), and
`$10` with weight `7 : 1` under the pill (the pill is believed to act on the copy); room policies
weighted `3 : 1` towards `$5`. `W10` is the mirror image. Every weight factors as
`f(s, k) · g(ö, a ∣ Π̈(s, k))`, which is what decision-determination clause (2) needs.
-/

set_option maxHeartbeats 1000000

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

namespace CB

/-- Worlds `((s, k), (ö, a))`.
Source: none: infrastructure (mandate T1)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := (Fin 2 × Fin 2) × (Fin 3 × Fin 2)

/-- The external action of dynamics `(s, k)` at instance `e`: `s` at `pre`, `$10` under the pill,
else `k`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def actOf (s k : Fin 2) (e : Fin 3) : Fin 2 := if e = 0 then s else if s = 1 then 1 else k

/-- The room payoff numerator: both `$5` → `1` (= `1/2`), both `$10` → `2` (= `1`), else `0`.
Source: [[communication-trust-translated]] line 149; mandate §3 (`$5 ↦ 1/2`, `$10 ↦ 1`)
Kind: D
Fidelity: exact (scaled to `[0,1]`)
Hyps: n/a -/
def pay (x y : Fin 2) : ℕ := if x = y then (if x = 1 then 2 else 1) else 0

/-- The utility numerator: `0` at `pre`, the room payoff of `(Ä, a)` at a room.
Source: mandate T1 ("at `pre` … else `0` … record the choice")
Kind: D
Fidelity: variant: `U = 0` at the pre-instance
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.2.1 = 0 then 0 else pay (actOf ω.1.1 ω.1.2 ω.2.1) ω.2.2

/-- Supporting lemma `u_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_le (ω : Ω) : u ω ≤ 2 := by revert ω; decide

/-- The chosen policy of dynamics `(s, k)`: `(0, s)` at `pre`, `(0, k)` at a room, whatever the
internal observation.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (s k : Fin 2) (oe : Fin 2 × Fin 3) : Fin 1 × Fin 2 := (0, if oe.2 = 0 then s else k)

/-- The side-channel impact: at a room, channel value `1` forces `$10`; nothing at `pre`.
Source: [[communication-trust-translated]] line 150 (the pill)
Kind: D
Fidelity: exact
Hyps: n/a -/
def pfun (e : Fin 3) (c : Fin 2) : Option (Fin 2) := if e = 0 then none else if c = 1 then some 1 else none

/-- **Coordinated Buttons as an abstract decision structure** over integer weights `W`.
Source: [[communication-trust-translated]] lines 148–158; mandate T1
Kind: N+
Fidelity: variant: the pill choice is `Ä(pre)` (module docstring); copies as a free coordinate (T8′); §3 (c)
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
    (fun ω₁ ω₂ => ((if ω₂.2.1 = 0 then actOf ω₁.1.1 ω₁.1.2 ω₁.2.1 else 0,
      actOf ω₁.1.1 ω₁.1.2 ω₁.2.1), ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((ω₁.1.1, ω₂.1.2), ω₁.2)) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₁.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **Coordinated Buttons as a concrete decision structure**: no messages; the pill forces `$10`
at the rooms.
Source: [[communication-trust-translated]] lines 148–158; mandate T1
Kind: N+
Fidelity: as `absDS`
Hyps: none -/
noncomputable def S (W : IntWeights Ω) : ConcreteDS Ω (Fin 2) (Fin 3) (Fin 1) (Fin 2) (Fin 2)
    (Fin 3 × Fin 2) (Fin 2) (Fin 1) (Fin 2) where
  toAbstractDS := absDS W
  s _ _ := none
  p := pfun

variable (W : IntWeights Ω)

/-! ### Reading `Π̈`, `Π*`, `R`, the modification event off the coordinates -/

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

/-- **`Π̈` on `CB`**: the external policy of dynamics `(s, k)` is `actOf s k`.
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

/-- Supporting lemma `evS_eq`: the event `{Π*(ȯ, ö) = a}` on the coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_eq (o : Fin 2) (e : Fin 3) (a : Fin 1 × Fin 2) :
    (S W).evS o e a = event fun ω : Ω => polOf' ω.1.1 ω.1.2 (o, e) = a := rfl

/-- **`Π* ⊑ D_{I,B}` on `CB`.**
Source: mandate T1(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem polS_sub : IsSubvariable (S W).DIB (S W).polS := by
  show ∀ ω ω' : Ω, (ω.1.1, ω.1.2) = (ω'.1.1, ω'.1.2) → polOf' ω.1.1 ω.1.2 = polOf' ω'.1.1 ω'.1.2
  decide +kernel

/-- **`R ⊑ D_{I,B}` on `CB`** (the recommendation is silent everywhere, so this is `rfl` — a
degenerate check).
Source: mandate T1(a)
Kind: N−
Fidelity: n/a (vacuous: `R` is constant)
Hyps: none -/
theorem R_sub_DIB : IsSubvariable (S W).DIB (S W).R := fun _ _ _ => rfl

/-- **`P(Π̈ = R) = 1` on `CB`**, vacuously: no message is ever sent, so `Follows` holds at every
world. Said plainly: this hypothesis of the repaired Self-Trust theorem carries no content here.
Source: mandate T1(c) ("no message sent: `R` silent, `Follows` vacuous — say so")
Kind: N−
Fidelity: n/a (vacuous)
Hyps: none -/
theorem followsR : mass (S W).μ.w (S W).evFollowsR = 1 := by
  have : (S W).evFollowsR = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ω
    rw [ConcreteDS.mem_evFollowsR]
    intro e a h
    exact absurd h (by simp [ConcreteDS.R, S])
  rw [this]
  exact mass_univ (S W).μ

/-- Supporting lemma `evMod_eq`: the modified worlds are those with the pill active.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evMod_eq : (S W).evMod = event fun ω : Ω => ω.1.1 = 1 := by
  ext ω
  simp only [ConcreteDS.evMod, mem_event]
  show (∃ e : Fin 3, (pfun e ω.1.1).isSome) ↔ ω.1.1 = 1
  revert ω
  decide +kernel

/-- Supporting lemma: attainment at the `pre` input.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_pre_nonempty (o : Fin 2) (x : Fin 2) : ((S W).evS o 0 (0, x)).Nonempty := by
  rw [evS_eq]; revert o x; decide +kernel

/-- Supporting lemma: attainment at a room input.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_room_nonempty (o : Fin 2) (e : Fin 3) (x : Fin 2) : ((S W).evS o e (0, x)).Nonempty := by
  rw [evS_eq]; revert o e x; decide +kernel

/-- **The pill is modifying with probability `1`, "nothing" with probability `0`** at the `pre`
input: `m(Π*(ȯ, pre) = pill) = 1`, `m(Π*(ȯ, pre) = nothing) = 0`.
Source: mandate T1(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem modS_pre (o : Fin 2) : (S W).modS o 0 (0, 1) = 1 ∧ (S W).modS o 0 (0, 0) = 0 := by
  unfold ConcreteDS.modS ConcreteDS.modProb
  rw [evMod_eq]
  constructor
  · refine condProbJunk_eq_one_of_subset (S W).pos (evS_pre_nonempty W o 1) ?_ 0
    rw [evS_eq]
    intro ω hω
    rw [mem_event] at hω ⊢
    revert ω o
    decide +kernel
  · refine condProbJunk_eq_zero_of_disjoint (S W).pos (evS_pre_nonempty W o 0) ?_ 0
    rw [evS_eq]
    revert o
    decide +kernel

/-- **The pill is not minimally modifying at `pre`**; "nothing" is.
Source: mandate T1(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_pill (o : Fin 2) : ¬ (S W).MinMod o 0 (0, 1) := by
  intro h
  have := h (0, 0) (evS_pre_nonempty W o 0)
  rw [(modS_pre W o).1, (modS_pre W o).2] at this
  linarith

/-- **"Nothing" is minimally modifying at `pre`.**
Source: mandate T1(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem minMod_nothing (o : Fin 2) : (S W).MinMod o 0 (0, 0) := by
  intro a' _
  rw [(modS_pre W o).2]
  unfold ConcreteDS.modS ConcreteDS.modProb
  exact ConcreteDS.condProbJunk_nonneg (S W).pos _ _

/-- **The prose meaning of `Π*` holds on `CB`**: at every world whose realized instance is
unforced, the effective action is the chosen one (`hlink` of `aE_follows_R_of_udtRuleAt`).
Source: mandate T1 (trap: "the pill is internal"), T7(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hlink : ∀ ω, (S W).P ω ((S W).oE ω) = none →
    (S W).polD ω ((S W).O ω) = (S W).polS ω ((S W).O ω) := by
  intro ω h
  have h' : pfun ω.2.1 ω.1.1 = none := h
  clear h
  rw [AbstractDS.polD_apply_O]
  show ((0 : Fin 1), actOf ω.1.1 ω.1.2 ω.2.1) = polOf' ω.1.1 ω.1.2 (ω.1.1, ω.2.1)
  revert ω
  decide +kernel

/-- **No instance receives a recommendation and a modification at once** on `CB`, vacuously (no
recommendation is ever made).
Source: mandate T7(d) (`hnosim`)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem hnosim : ∀ e o, ((S W).s e ((S W).projOH o)).isSome → (S W).p e ((S W).projOC o) = none :=
  fun _ _ h => absurd h (by simp [S])

/-! ### The score as a ratio of counts -/

/-- Supporting lemma `score_eq`: the score is the `u/2`-conditional expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem score_eq (o : Fin 2) (e : Fin 3) (a : Fin 1 × Fin 2) :
    (S W).score o e a = condExpJunk W.w (natDiv u 2) ((S W).evS o e a) (-1) := rfl

/-- **Strict score comparison from counts** on `CB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem score_lt_of_cnt {o : Fin 2} {e : Fin 3} {a b : Fin 1 × Fin 2}
    (ha : ((S W).evS o e a).Nonempty) (hb : ((S W).evS o e b).Nonempty)
    (h : csum W u ((S W).evS o e a) * W.cnt ((S W).evS o e b) <
      csum W u ((S W).evS o e b) * W.cnt ((S W).evS o e a)) :
    (S W).score o e a < (S W).score o e b := by
  rw [score_eq, score_eq]
  exact condExpJunk_natDiv_lt W u (by norm_num) ha hb h (-1)

/-! ### Decision-determination (prior-specific in clause (2)) -/

/-- Supporting lemma: `U` is a function of `E`, weight-free.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω, (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = (actOf ω'.1.1 ω'.1.2 ω'.2.1, ω'.2) →
    u ω = u ω' := by decide +kernel

/-- **Clause (1) of decision-determination on `CB`**: `U ⊑ E`, for every prior.
Source: mandate T1(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem U_sub_E : IsSubvariable (S W).E (S W).U := by
  intro ω ω' h
  show natDiv u 2 ω = natDiv u 2 ω'
  unfold natDiv
  rw [u_of_E ω ω' h]

/-- **Clause (2) of decision-determination on `CB` from a count identity** over the coordinates.
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

/-! ### The two priors -/

/-- The `$5`-concentrated coupling of the copy's action: see the module docstring.
Source: [[communication-trust-translated]] lines 152–153 ("sufficiently high prior expectation that you'll press the `$5` button")
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def wa5 (s k a : Fin 2) : ℕ :=
  if s = 1 then (if a = 1 then 7 else 1)
  else if k = 0 then (if a = 0 then 7 else 1) else (if a = 0 then 5 else 3)

/-- The `$5`-concentrated prior `W5`: room policies `3 : 1` towards `$5`; the copy's action
coupled by `wa5`; the pre-instance's dummy coordinate uniform. Not "copies in law" at
`k = $10`: the copy is believed to press `$5` `5 : 3` there, *anti*-correlated with the agent's
own policy (audit r1 fidelity B3). This is also why `CB W5` needs `Π̈(pre)` to be
decision-determined: with the choice hidden, the `Π̈`-atom `(rooms ↦ $10, $10)` would contain
both the pill worlds (copy `7 : 1` towards `$10`) and the `$10`-policy worlds without the pill
(copy `5 : 3` towards `$5`), and clause (2) fails there — machine-checked in repair round 2 on
the hidden-choice carrier, `CBh.not_decisionDetermined5` (`CoordButtonsHidden.lean`,
`3 · 48 ≠ 10 · 24`); `W10` has `wa10 0 1 = wa10 1 1` and does not have this problem
(`CBh.decisionDetermined10`).
Source: [[communication-trust-translated]] lines 152–153; mandate T1(b)
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def W5 : IntWeights Ω where
  wt ω := (if ω.1.2 = 0 then 3 else 1) * (if ω.2.1 = 0 then 4 else wa5 ω.1.1 ω.1.2 ω.2.2)
  pos ω := by revert ω; decide
  N := 192
  sum_eq := by decide +kernel

/-- The mirror coupling (`$10`-concentrated).
Source: mandate T1(b) ("with `W₁₀` the mirror")
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def wa10 (s k a : Fin 2) : ℕ :=
  if s = 1 then (if a = 1 then 7 else 1)
  else if k = 1 then (if a = 1 then 7 else 1) else (if a = 1 then 5 else 3)

/-- The `$10`-concentrated prior `W10`.
Source: mandate T1(b)
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def W10 : IntWeights Ω where
  wt ω := (if ω.1.2 = 1 then 3 else 1) * (if ω.2.1 = 0 then 4 else wa10 ω.1.1 ω.1.2 ω.2.2)
  pos ω := by revert ω; decide
  N := 192
  sum_eq := by decide +kernel

/-- **`CB.S W5` is decision-determined** — the check the corpus never made (udt-rep-024's flag):
clause (1) by `u_of_E`, clause (2) by the count identity over the coordinates.
Source: [[communication-trust-translated]] lines 148–158, 381–390; mandate T1(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined5 : (S W5).DecisionDetermined :=
  ⟨U_sub_E W5, dd2_of_cnt W5 (by decide +kernel)⟩

/-- **`CB.S W10` is decision-determined.**
Source: mandate T1(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined10 : (S W10).DecisionDetermined :=
  ⟨U_sub_E W10, dd2_of_cnt W10 (by decide +kernel)⟩

/-! ### T1(b): the two fixed points -/

/-- **Under `W5`, `$5` is strictly best at both room inputs**: for every internal observation `ȯ`
and room `e`, `E[U ∣ Π*(ȯ, e) = $10] < E[U ∣ Π*(ȯ, e) = $5]` (gap `7/16 − 5/12 = 1/48`).
Source: [[communication-trust-translated]] line 153 ("both red-room self and green-room self will prefer to press `$5`")
Kind: P
Fidelity: exact (computed on the witness)
Hyps: none -/
theorem score5_room (o : Fin 2) (e : Fin 3) (he : e ≠ 0) :
    (S W5).score o e (0, 1) < (S W5).score o e (0, 0) := by
  refine score_lt_of_cnt W5 (evS_room_nonempty W5 o e 1) (evS_room_nonempty W5 o e 0) ?_
  rw [evS_eq, evS_eq]
  revert o e
  decide +kernel

/-- **Under `W5`, the `$5`-pressing chosen policy satisfies the UDT rule at both room inputs**:
the "consistent equilibrium" of the paper's footnote, "if you expect that's what you'll end up
doing, then it is in fact what you end up doing", as a fixed point on the witness.
Two caveats (audit r1): the fixed point is of the rule *at the room inputs* — at `pre` the rule
selects the pill under both priors (`score5_pre`, `score10_pre`), so no `CB` world satisfies
the full `UdtRule`, and the "consistent equilibrium" on this witness is (pill, `$5` policy); and
the `$5` fixed point exists because `W5`'s belief about the copy leans `$5` *even when the
agent's own policy is `$10`* (`wa5 0 1 · = 5 : 3`), a belief the agent's own policy does not
move — on `CB`'s two-policy family a symmetric coupling makes `$10` win under every prior
(findings F-3, rescoped to this family in repair round 1).
Source: [[communication-trust-translated]] line 153 and its footnote (udt-rep-024(b))
Kind: P
Fidelity: variant: the pointwise rule at the room inputs only, at the `$5` worlds; the mechanism is `W5`'s copy-belief, not the source's "expectation about *your* button" (F-3)
Hyps: none; §3 (c) -/
theorem udtRuleAt5 (ω : Ω) (hk : ω.1.2 = 0) (o : Fin 2) (e : Fin 3) (he : e ≠ 0) :
    (S W5).UdtRuleAt ω o e := by
  intro a
  have hpol : (S W5).polS ω (o, e) = (0, 0) := by
    show polOf' ω.1.1 ω.1.2 (o, e) = (0, 0)
    unfold polOf'
    rw [if_neg he, hk]
  rw [hpol]
  obtain ⟨ai, x⟩ := a
  have : ai = 0 := Subsingleton.elim _ _
  subst this
  rcases fin2_cases x with rfl | rfl
  · exact le_rfl
  · exact (score5_room o e he).le

/-- **Under `W10`, `$10` is strictly best at both room inputs.**
Source: mandate T1(b) (the mirror)
Kind: P
Fidelity: exact (computed)
Hyps: none -/
theorem score10_room (o : Fin 2) (e : Fin 3) (he : e ≠ 0) :
    (S W10).score o e (0, 0) < (S W10).score o e (0, 1) := by
  refine score_lt_of_cnt W10 (evS_room_nonempty W10 o e 0) (evS_room_nonempty W10 o e 1) ?_
  rw [evS_eq, evS_eq]
  revert o e
  decide +kernel

/-- **Under `W10`, the `$10`-pressing chosen policy satisfies the UDT rule at both room inputs.**
Source: mandate T1(b) (the mirror fixed point)
Kind: P
Fidelity: exact
Hyps: none; §3 (c) -/
theorem udtRuleAt10 (ω : Ω) (hk : ω.1.2 = 1) (o : Fin 2) (e : Fin 3) (he : e ≠ 0) :
    (S W10).UdtRuleAt ω o e := by
  intro a
  have hpol : (S W10).polS ω (o, e) = (0, 1) := by
    show polOf' ω.1.1 ω.1.2 (o, e) = (0, 1)
    unfold polOf'
    rw [if_neg he, hk]
  rw [hpol]
  obtain ⟨ai, x⟩ := a
  have : ai = 0 := Subsingleton.elim _ _
  subst this
  rcases fin2_cases x with rfl | rfl
  · exact (score10_room o e he).le
  · exact le_rfl

/-! ### T1(c): self-trust fails without communicative alternatives -/

/-- **Under `W5` the pill is strictly preferred at the `pre` input**:
`E[U ∣ Π*(ȯ, pre) = nothing] = 54/192 = 9/32 < 7/12 = 112/192 = E[U ∣ Π*(ȯ, pre) = pill]`
(the conditioning events `{Π*(ȯ, pre) = a}` contain the `pre` worlds, where `U = 0`, which
dilute both sides; the glosses `9/64 < 7/24` of the first report were wrong — audit r1 N1).
Source: [[communication-trust-translated]] line 153 ("If you anticipate this, then you will prefer to take the pill")
Kind: P
Fidelity: exact (computed)
Hyps: none -/
theorem score5_pre (o : Fin 2) : (S W5).score o 0 (0, 0) < (S W5).score o 0 (0, 1) := by
  refine score_lt_of_cnt W5 (evS_pre_nonempty W5 o 0) (evS_pre_nonempty W5 o 1) ?_
  rw [evS_eq, evS_eq]
  revert o
  decide +kernel

/-- **Under `W10` the pill is still strictly preferred at the `pre` input**
(`E[U ∣ nothing] = 90/192 = 15/32 < 7/12 = E[U ∣ pill]`; the first report's `45/128` and `7/24`
were wrong glosses — audit r1 N1):
under `W10` "nothing" leaves policy uncertainty that the pill removes, so the paper's "be
indifferent about taking the pill" needs certainty about one's own policy, which the support
convention excludes (findings F-4). This is **not** a fact about every full-support prior
(the first version of F-4 said so; audit r2 fidelity B1): it needs the pill to be believed to
reach the copy at least as well as the agent's own `$10` policy does, which `W10` assumes
(`7 : 1` under both) and `WN` below denies — there "nothing" beats the pill
(`nothing_beats_pillN`).
Source: [[communication-trust-translated]] line 152 ("be indifferent about taking the pill"); mandate §6.13
Kind: P
Fidelity: exact (computed; a finding)
Hyps: none -/
theorem score10_pre (o : Fin 2) : (S W10).score o 0 (0, 0) < (S W10).score o 0 (0, 1) := by
  refine score_lt_of_cnt W10 (evS_pre_nonempty W10 o 0) (evS_pre_nonempty W10 o 1) ?_
  rw [evS_eq, evS_eq]
  revert o
  decide +kernel

/-- **The repaired Self-Trust conclusion fails on `CB.S W5` at the `pre` input**: no action is
both minimally modifying and a UDT argmax — the pill is the unique argmax and is not minimally
modifying — while decision-determination, `Π* ⊑ D_{I,B}`, `R ⊑ D_{I,B}` and `P(Π̈ = R) = 1`
(vacuously) all hold. So `selfTrust_repaired`'s communicative-alternatives hypothesis is not
redundant.
Source: mandate T1(c) (load-bearing 1)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_argmax5 (o : Fin 2) :
    ¬ ∃ a, (S W5).MinMod o 0 a ∧ IsArgmax ((S W5).score o 0) a := by
  rintro ⟨⟨ai, x⟩, hmm, harg⟩
  have : ai = 0 := Subsingleton.elim _ _
  subst this
  rcases fin2_cases x with rfl | rfl
  · exact absurd (harg (0, 1)) (not_le.2 (score5_pre o))
  · exact not_minMod_pill W5 o hmm

/-- **`CB.S W5` has no communicative alternatives** — by contraposition of the repaired
Self-Trust theorem, whose other hypotheses hold.
Source: mandate T1(c)
Kind: C
Fidelity: n/a
Hyps: (a) `selfTrust_repaired`; §3 (c) -/
theorem not_hasCA5_of_selfTrust : ¬ (S W5).HasCA := fun hCA =>
  not_minMod_argmax5 0
    ((S W5).selfTrust_repaired decisionDetermined5 (polS_sub W5) (R_sub_DIB W5) hCA (followsR W5) 0 0)

/-- **`CB.S W5` has no communicative alternatives, directly**: the only minimally modifying
action at `pre` is "nothing", and the law of `Π̈` given "nothing" puts mass `0` on the pill
profile `(pre ↦ $10, red ↦ $10, green ↦ $10)`, which has mass `1` given the pill. Unlike the
Memory Problem's (`Mem.not_isCA_pill`), this failure is robust to the `Π̈(pre)` leak (F-1): on
the room coordinates alone, `P(rooms = ($10, $10) ∣ nothing) = P(k = $10) = 1/4 ≠ 1 =
P(rooms = ($10, $10) ∣ pill)` — the pill changes the law of the rooms' actions, the paper's
reason (audit r1 fidelity N5).
Source: mandate T1(c)
Kind: P
Fidelity: n/a
Hyps: none -/
theorem not_hasCA5 : ¬ (S W5).HasCA := by
  intro h
  obtain ⟨⟨ai, x⟩, hmm, hca⟩ := h 0 0 (0, 1) (evS_pre_nonempty W5 0 1)
  have : ai = 0 := Subsingleton.elim _ _
  subst this
  rcases fin2_cases x with rfl | rfl
  · have := hca fun e => actOf 1 0 e
    rw [(ConcreteDS.evFollowsR_eq_univ_iff (S W5)).1 (followsR W5), Finset.inter_univ,
      evPolE_eq] at this
    rw [condProbJunk_eq_one_of_subset (S W5).pos (evS_pre_nonempty W5 0 1) ?_,
      condProbJunk_eq_zero_of_disjoint (S W5).pos (evS_pre_nonempty W5 0 0) ?_] at this
    · exact one_ne_zero this
    · rw [evS_eq]; decide +kernel
    · rw [evS_eq]
      intro ω hω
      rw [mem_event] at hω ⊢
      revert ω
      decide +kernel
  · exact not_minMod_pill W5 0 hmm

/-! ### Repair round 2: the pill overrides a `$5` press; a prior under which "nothing" wins -/

/-- **At a `$5`-policy pill world the pill overrides the chosen `$5` press at the realized room
input**: `Π†(ω)(Ȯ, Ö) = $10 ≠ $5 = Π*(ω)(Ȯ, Ö)`, for every prior and both copy actions. `CB`'s
chosen policy presses `k` at a room whatever it observes (`polOf'`), so the forcing changes the
behaviour — the source's own reason for the pill ("if you anticipate [pressing `$5`] … you will
prefer to take the pill", line 153). Lifted from the audit-r2 probes `CbHarmfulForcing` /
`CbPillOverridesPolicy`. Contrast `pill_harmless_ten`, and `CBm`/`TB`, whose chosen policies
read the channel and press `$10` on an active one.
Source: [[communication-trust-translated]] line 153; audit r2 (fidelity B2, adversarial B1)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem pill_overrides_five (e : Fin 3) (a : Fin 2) (he : e ≠ 0) :
    (S W).polD ((1, 0), (e, a)) ((S W).O ((1, 0), (e, a))) ≠
      (S W).polS ((1, 0), (e, a)) ((S W).O ((1, 0), (e, a))) := by
  rw [AbstractDS.polD_apply_O]
  show ((0 : Fin 1), actOf 1 0 e) ≠ polOf' 1 0 (1, e)
  revert e
  decide

/-- **At a `$10`-policy pill world the forcing is harmless at the realized input**:
`Π†(ω)(Ȯ, Ö) = Π*(ω)(Ȯ, Ö)` — the chosen policy presses `$10` anyway. So on `CB` the pill is
harmless forcing at the `$10`-policy worlds and a behavioural modification at the `$5`-policy
worlds (`pill_overrides_five`): `m(pill) = 1` counts forcing that is behavioural with
probability `P(k = $5)` (findings F-9 (ii), corrected in repair round 2).
Source: audit r2 (fidelity B2, adversarial B1)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pill_harmless_ten (e : Fin 3) (a : Fin 2) :
    (S W).polD ((1, 1), (e, a)) ((S W).O ((1, 1), (e, a))) =
      (S W).polS ((1, 1), (e, a)) ((S W).O ((1, 1), (e, a))) := by
  rw [AbstractDS.polD_apply_O]
  show ((0 : Fin 1), actOf 1 1 e) = polOf' 1 1 (1, e)
  revert e
  decide

/-- The copy's law under `WN`: a fair coin under the pill (`4 : 4`, so that every `(s, k)` carries
the same mass as under `W5`/`W10`); `7 : 1` towards the agent's chosen room policy otherwise.
The pill is *not* believed to reach the copy.
Source: audit r2 (fidelity B1, probe `F4EveryPrior`, with the pill's copy weights renormalized)
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def waN (s k a : Fin 2) : ℕ := if s = 1 then 4 else (if a = k then 7 else 1)

/-- **The boundary prior `WN`**: room policies `3 : 1` towards `$10`, pre dummy uniform, the copy
by `waN`; total `192`. A full-support, decision-determined prior on `CB.Ω` under which "nothing"
strictly beats the pill at `pre` (`nothing_beats_pillN`): the counterexample to the first
version of findings F-4 ("the pill is strictly preferred at `pre` under *every* prior").
Source: audit r2 (fidelity B1, probe `F4EveryPrior`)
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def WN : IntWeights Ω where
  wt ω := (if ω.1.2 = 1 then 3 else 1) * (if ω.2.1 = 0 then 4 else waN ω.1.1 ω.1.2 ω.2.2)
  pos ω := by revert ω; decide
  N := 192
  sum_eq := by decide +kernel

/-- **`CB.S WN` is decision-determined** (both clauses): the two pill dynamics share the
`Π̈`-atom `(pre ↦ pill, $10, $10)` and the copy's law under the pill does not depend on `k`, so
the counterexample lies inside the paper's own conditions.
Source: audit r2 (fidelity B1)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDeterminedN : (S WN).DecisionDetermined :=
  ⟨U_sub_E WN, dd2_of_cnt WN (by decide +kernel)⟩

/-- **Under `WN` "nothing" strictly beats the pill at every `pre` input**:
`E[U ∣ pill] = 1/3 < 49/96 = E[U ∣ nothing]` (room-conditional `1/2 < 49/64`; the `pre` worlds
dilute both sides equally under this prior). So the pill's strict preference at `pre`
(`score5_pre`, `score10_pre`) is not a theorem about every full-support prior: with
`q = P(copy = $10 ∣ pill)`, `q₁ = P(copy = $10 ∣ $10 policy, no pill)`,
`q₀ = P(copy = $5 ∣ $5 policy, no pill)` and `p = P(k = $10)`, the room-conditional values are
`E[U ∣ pill] = q` and `E[U ∣ nothing] = p · q₁ + (1 − p) · q₀ / 2`, so the pill wins for every
`p < 1` iff `q ≥ q₁` and `q > q₀ / 2` (`W10`: `q = q₁ = 7/8`, `q₀ = 5/8`; `W5`: `q = 7/8 > 3/8 = q₁`;
`WN`: `q = 1/2 < 7/8 = q₁`). Findings F-4, rescoped in repair round 2.
Source: [[communication-trust-translated]] line 152; audit r2 (fidelity B1, probe `F4EveryPrior`)
Kind: N+
Fidelity: exact (computed; the boundary case of F-4)
Hyps: none -/
theorem nothing_beats_pillN (o : Fin 2) : (S WN).score o 0 (0, 1) < (S WN).score o 0 (0, 0) := by
  refine score_lt_of_cnt WN (evS_pre_nonempty WN o 1) (evS_pre_nonempty WN o 0) ?_
  rw [evS_eq, evS_eq]
  revert o
  decide +kernel

end CB

end Cleanroom.Udt.UdtCtExamples
