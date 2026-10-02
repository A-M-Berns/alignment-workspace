import Cleanroom.Udt.UdtCommTrust.Advice
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCtExamples.CountExt

/-!
# `Cleanroom.Udt.UdtCtExamples.ThirdButton`: the Third Button problem (T3(a)–(c))

Work package `udt-ct-examples`, target T3. Source: [[communication-trust-translated]] lines
171–181 (the example; "each copy would trust that the other copy will follow this instruction;
however, if that were true, *this would lead both copies to choose `$20`*, resulting in a payoff
of `$0`"; "Depending on its prior, UDT may still need to use the pill"), [[examples-revisited]]
Example 3 (corrected 2026-08-05: the symmetric-reasoning reply "is again a fixed-point-selection
argument").

## The structure `TB.S W`

Worlds `((s, t), (ö, a))`, 24 of them: `s : Fin 2` the channel state and the pre-instance's
choice (`0` the pill, active at both rooms; `1` the message "press `$10`", sent to both rooms —
`R ω red = R ω green`, the paper's "you cannot tell yourself to do different things depending on
the color of the room"); `t : Fin 2` the chosen room policy when told `$10`: `0` follow, `1`
exploit (press `$20`); `ö : Fin 3` the focal instance (`pre`, red, green); `a : Fin 2` the other
room's action (`0` = `$10`, `1` = `$20`), free, coupled in law. `AE = Fin 2` at the rooms: `$10`,
`$20` — the `$5` button plays no part in the source's analysis and is dropped (with it the
"nothing" pre-choice: `E_fac` needs the rooms to realize every value `Ä(pre)` takes). Same
representation as `CB` (report §0.1): the choice is `Ä(pre) = s`, `Ȯ = Ǒ = Ô = D_I = s`,
`D_B = t`, `AI = Fin 1` (which `StableR`/`Stable` need: with `|AI| ≥ 2` the junk `−1` makes
them unsatisfiable, `udt-comm-trust` `Concrete.lean`). Payoffs: both `$10` → `1/2`, `$10`/`$20`
→ `1`, both `$20` → `0` (`u/2`); `0` at `pre`.

## Two priors, because the source's two claims need incompatible beliefs

`Wfi` (functional identity): the copy's action follows the agent's own external policy at the
other room `3 : 1`; the exploiting policy weighted `3 : 1` ("chosen policies best-respond").
`Wnt` (naive trust): as `Wfi`, except that when the agent's policy exploits a message the copy
is believed to *follow* it `7 : 1`. Under `Wnt` the message is unstable at the rooms (T3(b)) and
the message beats the pill at `pre`; under `Wfi` the message is stable in the told form and the
pill beats the message at `pre` (T3(c)). The sign identity behind this is in the findings (F-5):
with the pre-action silent about the room policy and decision-determination, "exploiting beats
following given told" and "the message beats the pill at `pre`" have the same sign.
-/

set_option maxHeartbeats 1000000

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

namespace TB

/-- Worlds `((s, t), (ö, a))`.
Source: none: infrastructure (mandate T3)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := (Fin 2 × Fin 2) × (Fin 3 × Fin 2)

/-- The external action of dynamics `(s, t)` at instance `e`: `s` at `pre`; `$10` under the pill;
`t`'s response to the message at a room.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def actOf (s t : Fin 2) (e : Fin 3) : Fin 2 := if e = 0 then s else if s = 0 then 0 else t

/-- The payoff numerator on `{$10, $20}`: both `$10` → `1`, mixed → `2`, both `$20` → `0`.
Source: [[communication-trust-translated]] line 172; mandate §3 (`$20 ↦ 1`, `$10 ↦ 1/2`)
Kind: D
Fidelity: exact on the two buttons kept
Hyps: n/a -/
def pay (x y : Fin 2) : ℕ := if x = y then (if x = 0 then 1 else 0) else 2

/-- The utility numerator.
Source: mandate T3
Kind: D
Fidelity: variant: `0` at `pre`
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.2.1 = 0 then 0 else pay (actOf ω.1.1 ω.1.2 ω.2.1) ω.2.2

/-- Supporting lemma `u_le`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_le (ω : Ω) : u ω ≤ 2 := by revert ω; decide

/-- The chosen policy of dynamics `(s, t)`: `s` at `pre`; at a room, `$10` when the internal
observation shows the pill, `t`'s response when it shows the message.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polOf' (s t : Fin 2) (oe : Fin 2 × Fin 3) : Fin 1 × Fin 2 :=
  (0, if oe.2 = 0 then s else if oe.1 = 0 then 0 else t)

/-- The message semantics: at a room, channel value `1` recommends `$10`; nothing at `pre`.
Source: [[communication-trust-translated]] line 172 ("telling yourself to press `$10` buttons")
Kind: D
Fidelity: exact
Hyps: n/a -/
def sfun (e : Fin 3) (h : Fin 2) : Option (Fin 2) := if e ≠ 0 ∧ h = 1 then some 0 else none

/-- The side-channel impact: at a room, channel value `0` forces `$10`.
Source: [[communication-trust-translated]] line 172 (the pill)
Kind: D
Fidelity: exact
Hyps: n/a -/
def pfun (e : Fin 3) (c : Fin 2) : Option (Fin 2) := if e ≠ 0 ∧ c = 0 then some 0 else none

/-- **The Third Button problem as an abstract decision structure** over weights `W`.
Source: [[communication-trust-translated]] lines 171–181; mandate T3
Kind: N+
Fidelity: variant: choice as `Ä(pre)` (§0.1); copies in law (T8′); `$5` dropped, and with it the "nothing" pre-choice (the source offers pill, message, or neither; `E_fac` forces the rooms to realize every value of `Ä(pre)`); §3 (c)
Hyps: none -/
noncomputable def absDS (W : IntWeights Ω) : AbstractDS Ω (Fin 2) (Fin 3) (Fin 1) (Fin 2) (Fin 2)
    (Fin 3 × Fin 2) (Fin 2) (Fin 2) (Fin 2) where
  μ := W.dist
  pos := W.w_pos
  oI ω := ω.1.1
  oE ω := ω.2.1
  aI _ := 0
  aE ω := actOf ω.1.1 ω.1.2 ω.2.1
  dI ω := ω.1.1
  dE ω := ω.2
  dB ω := ω.1.2
  oH ω := ω.1.1
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
    (fun ω₁ ω₂ => ((if ω₂.2.1 = 0 then actOf ω₁.1.1 ω₁.1.2 ω₁.2.1 else 1,
      actOf ω₁.1.1 ω₁.1.2 ω₁.2.1), ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((ω₁.1.1, ω₂.1.2), ω₁.2)) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₁.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **The Third Button problem as a concrete decision structure.**
Source: [[communication-trust-translated]] lines 171–181; mandate T3
Kind: N+
Fidelity: as `absDS`
Hyps: none -/
noncomputable def S (W : IntWeights Ω) : ConcreteDS Ω (Fin 2) (Fin 3) (Fin 1) (Fin 2) (Fin 2)
    (Fin 3 × Fin 2) (Fin 2) (Fin 2) (Fin 2) where
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
    (∀ ω : Ω, actOf ω.1.1 ω.1.2 ω.2.1 = actOf ω.1.1 ω.1.2 ω.2.1) ∧
    (∀ ω ω' : Ω, (ω.1.1, ω.1.2) = (ω'.1.1, ω'.1.2) →
      (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf ω'.1.1 ω'.1.2 e) ∧
    (∀ (ω : Ω) (e : Fin 3), ∃ ω' : Ω, (ω'.1.1, ω'.1.2) = (ω.1.1, ω.1.2) ∧ ω'.2.1 = e) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`Π̈` on `TB`.**
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

/-- Supporting lemma `evS_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_eq (o : Fin 2) (e : Fin 3) (a : Fin 1 × Fin 2) :
    (S W).evS o e a = event fun ω : Ω => polOf' ω.1.1 ω.1.2 (o, e) = a := rfl

/-- Supporting lemma `projOH_eq`: every internal observation is realized, so the projection is
the identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOH_eq (o : Fin 2) : (S W).projOH o = o := (S W).projOH_oI (((o, 0), (0, 0)) : Ω)

/-- Supporting lemma `projOC_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem projOC_eq (o : Fin 2) : (S W).projOC o = o := (S W).projOC_oI (((o, 0), (0, 0)) : Ω)

/-- **`Π* ⊑ D_{I,B}` on `TB`.**
Source: mandate T3(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem polS_sub : IsSubvariable (S W).DIB (S W).polS := by
  show ∀ ω ω' : Ω, (ω.1.1, ω.1.2) = (ω'.1.1, ω'.1.2) → polOf' ω.1.1 ω.1.2 = polOf' ω'.1.1 ω'.1.2
  decide +kernel

/-- **`R ⊑ D_{I,B}` on `TB`.**
Source: mandate T3(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem R_sub_DIB : IsSubvariable (S W).DIB (S W).R := by
  show ∀ ω ω' : Ω, (ω.1.1, ω.1.2) = (ω'.1.1, ω'.1.2) →
    (fun e => sfun e ω.1.1) = fun e => sfun e ω'.1.1
  decide +kernel

/-- **The recommendation is the same at both rooms** — "you cannot tell yourself to do
different things depending on the color of the room".
Source: [[communication-trust-translated]] line 172; mandate T3(a)
Kind: L
Fidelity: exact
Hyps: none -/
theorem R_symm (ω : Ω) : (S W).R ω 1 = (S W).R ω 2 := by
  show sfun 1 ω.1.1 = sfun 2 ω.1.1
  revert ω
  decide +kernel

/-- The recommendation realized at the message worlds: `$10` at both rooms, silent at `pre`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def r₀ : Fin 3 → Option (Fin 2) := fun e => sfun e 1

/-- Supporting lemma `r₀_realized`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem r₀_realized : r₀ ∈ Set.range (S W).R := ⟨((1, 0), (0, 0)), rfl⟩

/-- Supporting lemma `evMod_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evMod_eq : (S W).evMod = event fun ω : Ω => ω.1.1 = 0 := by
  ext ω
  simp only [ConcreteDS.evMod, mem_event]
  show (∃ e : Fin 3, (pfun e ω.1.1).isSome) ↔ ω.1.1 = 0
  revert ω
  decide +kernel

/-- Supporting lemma: attainment at the pre input.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_pre_nonempty (o : Fin 2) (x : Fin 2) : ((S W).evS o 0 (0, x)).Nonempty := by
  rw [evS_eq]; revert o x; decide +kernel

/-- Supporting lemma: attainment at the message-observed room inputs.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_msg_nonempty (e : Fin 3) (he : e ≠ 0) (x : Fin 2) : ((S W).evS 1 e (0, x)).Nonempty := by
  rw [evS_eq]; revert e x; decide +kernel

/-- **The prose meaning of `Π*` holds on `TB`** (`hlink`).
Source: mandate T7(d)
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

/-- **No instance receives a recommendation and a modification at once** on `TB` (`hnosim`):
the message and the pill are exclusive channel states.
Source: mandate T7(d)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hnosim : ∀ e o, ((S W).s e ((S W).projOH o)).isSome → (S W).p e ((S W).projOC o) = none := by
  intro e o h
  rw [projOH_eq] at h
  rw [projOC_eq]
  have h' : (sfun e o).isSome := h
  clear h
  show pfun e o = none
  revert e o
  decide +kernel

/-- **The pill is modifying with probability `1`, the message with probability `0`** at the pre
input.
Source: mandate T3(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem modS_pre (o : Fin 2) : (S W).modS o 0 (0, 0) = 1 ∧ (S W).modS o 0 (0, 1) = 0 := by
  unfold ConcreteDS.modS ConcreteDS.modProb
  rw [evMod_eq]
  constructor
  · refine condProbJunk_eq_one_of_subset (S W).pos (evS_pre_nonempty W o 0) ?_ 0
    rw [evS_eq]
    intro ω hω
    rw [mem_event] at hω ⊢
    revert ω o
    decide +kernel
  · refine condProbJunk_eq_zero_of_disjoint (S W).pos (evS_pre_nonempty W o 1) ?_ 0
    rw [evS_eq]
    revert o
    decide +kernel

/-- **The pill is not minimally modifying at the pre input; the message is.**
Source: mandate T3(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_pill (o : Fin 2) : ¬ (S W).MinMod o 0 (0, 0) ∧ (S W).MinMod o 0 (0, 1) := by
  constructor
  · intro h
    have := h (0, 1) (evS_pre_nonempty W o 1)
    rw [(modS_pre W o).1, (modS_pre W o).2] at this
    linarith
  · intro a' _
    rw [(modS_pre W o).2]
    unfold ConcreteDS.modS ConcreteDS.modProb
    exact ConcreteDS.condProbJunk_nonneg (S W).pos _ _

/-- **`P(Π̈ = R) < 1` on `TB`** for every prior: the worlds where the message is sent and the
chosen policy exploits it do not follow the recommendation. So the repaired Self-Trust theorem's
third hypothesis fails on the Third Button — this, not the failure of communicative
alternatives, is where the example leaves the theorem's scope on this witness.
Source: [[communication-trust-translated]] lines 173–174; mandate T3(c)
Kind: P
Fidelity: exact
Hyps: none -/
theorem followsR_lt_one : mass (S W).μ.w (S W).evFollowsR < 1 := by
  have hne : (S W).evFollowsR ≠ univ := by
    intro h
    have := (Finset.eq_univ_iff_forall.1 h) (((1, 1), (0, 0)) : Ω)
    rw [ConcreteDS.mem_evFollowsR, polE_eq] at this
    have h2 : ¬ ConcreteDS.Follows (fun e => actOf 1 1 e) (fun e => sfun e 1) := by decide
    exact h2 this
  have h1 := (ConcreteDS.evFollowsR_eq_univ_iff (S W)).not.2 hne
  have hle : mass (S W).μ.w (S W).evFollowsR ≤ 1 := by
    rw [← mass_univ (S W).μ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun ω _ _ => ((S W).pos ω).le
  exact lt_of_le_of_ne hle h1

/-- **The message is not a communicative alternative of the pill at the pre input** — but for
the representation's reason, not the paper's: `Π̈(pre)` is the choice itself, so the two laws
of `Π̈` differ at the pre coordinate (report §0.1, findings F-1). The substantive obstruction on
this witness is `followsR_lt_one`.
Source: mandate T3(c)
Kind: N−
Fidelity: weaker: holds through the representation (flagged; Kind regraded from `L`, audit r2 adversarial N5)
Hyps: none -/
theorem not_isCA_pill_msg (o : Fin 2) : ¬ (S W).IsCA o 0 (0, 0) (0, 1) := by
  rintro ⟨-, hca⟩
  have := hca fun e => actOf 0 0 e
  have hdisj : (S W).evPolE (fun e => actOf 0 0 e) ∩ (S W).evS o 0 (0, 1) = ∅ := by
    rw [evPolE_eq, evS_eq]; exact isCA_key₁ o
  have hsub : (S W).evS o 0 (0, 0) ⊆ (S W).evPolE (fun e => actOf 0 0 e) := by
    rw [evPolE_eq, evS_eq]
    intro ω hω
    rw [mem_event] at hω ⊢
    exact isCA_key₂ o ω hω
  have hne : ((S W).evS o 0 (0, 1) ∩ (S W).evFollowsR).Nonempty := by
    refine ⟨((1, 0), (0, 0)), Finset.mem_inter.2 ⟨?_, ?_⟩⟩
    · rw [evS_eq, mem_event]; exact isCA_key₃ o
    · rw [ConcreteDS.mem_evFollowsR, polE_eq]
      show ConcreteDS.Follows (fun e => actOf 1 0 e) (fun e => sfun e 1)
      decide
  rw [condProbJunk_eq_one_of_subset (S W).pos (evS_pre_nonempty W o 0) hsub,
    condProbJunk_eq_zero_of_disjoint (S W).pos hne
      (by rw [← Finset.inter_assoc, hdisj, Finset.empty_inter])] at this
  exact one_ne_zero this
where
  isCA_key₁ : ∀ o : Fin 2,
      (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 0 0 e) ∩
        event (fun ω : Ω => polOf' ω.1.1 ω.1.2 (o, 0) = (0, 1)) = ∅ := by decide +kernel
  isCA_key₂ : ∀ (o : Fin 2) (ω : Ω), polOf' ω.1.1 ω.1.2 (o, 0) = (0, 0) →
      (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf 0 0 e := by decide +kernel
  isCA_key₃ : ∀ o : Fin 2, polOf' 1 0 (o, 0) = (0, 1) := by decide

/-! ### Scores as counts -/

/-- Supporting lemma `score_lt_of_cnt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem score_lt_of_cnt {o : Fin 2} {e : Fin 3} {a b : Fin 1 × Fin 2}
    (ha : ((S W).evS o e a).Nonempty) (hb : ((S W).evS o e b).Nonempty)
    (h : csum W u ((S W).evS o e a) * W.cnt ((S W).evS o e b) <
      csum W u ((S W).evS o e b) * W.cnt ((S W).evS o e a)) :
    (S W).score o e a < (S W).score o e b :=
  condExpJunk_natDiv_lt W u (by norm_num) ha hb h (-1)

/-- Supporting lemma `evToldMinus_eq`: the told event on the coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evToldMinus_eq (r : Fin 3 → Option (Fin 2)) (e : Fin 3) :
    (S W).evToldMinus r e = event fun ω : Ω => ∀ e' ≠ e, sfun e' ω.1.1 = r e' := by
  ext ω
  simp only [ConcreteDS.evToldMinus, mem_event]
  exact Iff.rfl

/-- Supporting lemma `evFollowsMinus_eq`: the follows event on the coordinates.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evFollowsMinus_eq (r : Fin 3 → Option (Fin 2)) (e : Fin 3) :
    (S W).evFollowsMinus r e =
      event fun ω : Ω => ∀ e' ≠ e, ∀ a, r e' = some a → actOf ω.1.1 ω.1.2 e' = a := by
  ext ω
  simp only [ConcreteDS.evFollowsMinus, mem_event, polE_eq]

/-! ### Decision-determination for both priors -/

/-- Supporting lemma: `U ⊑ E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω, (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = (actOf ω'.1.1 ω'.1.2 ω'.2.1, ω'.2) →
    u ω = u ω' := by decide +kernel

/-- **Clause (2) of decision-determination from a count identity** (any prior).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined_of_cnt
    (key : ∀ (e : Fin 2 × (Fin 3 × Fin 2)) (d : Fin 2 × Fin 2),
      W.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = e ∧ (ω.1.1, ω.1.2) = d) *
          W.cnt (event fun ω : Ω => (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e) =
        W.cnt (event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = e ∧
            (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e) *
          W.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = d)) :
    (S W).DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · show natDiv u 2 ω = natDiv u 2 ω'
    unfold natDiv
    rw [u_of_E ω ω' h]
  · have hev : (event fun ω => (S W).E ω = e ∧ (S W).polE ω = (S W).polOf d) =
        event fun ω : Ω => (actOf ω.1.1 ω.1.2 ω.2.1, ω.2) = e ∧
          (fun e => actOf ω.1.1 ω.1.2 e) = fun e => actOf d.1 d.2 e :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]; rfl
    rw [hev, evPolE_eq, polOf_eq]
    exact W.mass_mul_eq_of_cnt (key e d)

/-- The functional-identity prior `Wfi` (module docstring).
Source: mandate T3(c) ("trusting weights"), read as: the copy runs the agent's policy
Kind: D
Fidelity: n/a (a prior)
Hyps: n/a -/
def Wfi : IntWeights Ω where
  wt ω := (if ω.1.2 = 1 then 3 else 1) *
    (if ω.2.1 = 0 then 4 else if ω.2.2 = actOf ω.1.1 ω.1.2 1 then 3 else 1)
  pos ω := by revert ω; decide
  N := 128
  sum_eq := by decide +kernel

/-- The naive-trust prior `Wnt`: as `Wfi`, but when the agent exploits a message the copy is
believed to follow it `7 : 1`.
Source: [[communication-trust-translated]] line 173 ("each copy would trust that the other copy will follow this instruction"); mandate T3(b)
Kind: D
Fidelity: n/a (a prior; ATTRIBUTION-UNVETTED that "trust" means this)
Hyps: n/a -/
def Wnt : IntWeights Ω where
  wt ω := (if ω.1.2 = 1 then 3 else 1) *
    (if ω.2.1 = 0 then 4 else if ω.1.1 = 1 ∧ ω.1.2 = 1 then (if ω.2.2 = 0 then 7 else 1)
      else if ω.2.2 = actOf ω.1.1 ω.1.2 1 then 3 else 1)
  pos ω := by revert ω; decide
  N := 152
  sum_eq := by decide +kernel

/-- **`TB.S Wfi` is decision-determined.**
Source: mandate T3(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined_fi : (S Wfi).DecisionDetermined :=
  decisionDetermined_of_cnt Wfi (by decide +kernel)

/-- **`TB.S Wnt` is decision-determined.**
Source: mandate T3(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined_nt : (S Wnt).DecisionDetermined :=
  decisionDetermined_of_cnt Wnt (by decide +kernel)

/-! ### T3(b): under naive trust the recommendation is unstable and Advice-Following fails -/

/-- **Under `Wnt`, given the other room was told `$10`, exploiting beats following at the
message-observed red input**: `E[U ∣ Π*(msg, red) = $10, R(green) = $10] = 5/8 < 7/8 =
E[U ∣ Π*(msg, red) = $20, R(green) = $10]` (on the worlds' `u/2` scale, as counts).
Source: [[communication-trust-translated]] line 173; mandate T3(b) (load-bearing)
Kind: P
Fidelity: exact (computed)
Hyps: none -/
theorem told_exploit_gt :
    condExpJunk (S Wnt).μ.w (S Wnt).U ((S Wnt).evS 1 1 (0, 0) ∩ (S Wnt).evToldMinus r₀ 1) (-1) <
      condExpJunk (S Wnt).μ.w (S Wnt).U ((S Wnt).evS 1 1 (0, 1) ∩ (S Wnt).evToldMinus r₀ 1) (-1) := by
  refine condExpJunk_natDiv_lt Wnt u (by norm_num) ?_ ?_ ?_ (-1)
  · rw [evS_eq, evToldMinus_eq]; decide +kernel
  · rw [evS_eq, evToldMinus_eq]; decide +kernel
  · rw [evS_eq, evS_eq, evToldMinus_eq]; decide +kernel

/-- **The recommendation "`$10` at both rooms" is not stable in the told form under `Wnt`.**
Source: [[communication-trust-translated]] lines 173, 491–495; mandate T3(b)
Kind: P
Fidelity: exact
Hyps: none -/
theorem not_stableR_nt : ¬ (S Wnt).StableR r₀ := by
  intro h
  have := h 1 0 (by decide) 1 (by rw [projOH_eq]; decide +kernel) 0 1 (by decide)
  exact absurd told_exploit_gt (not_lt.2 this.le)

/-- **Given the other room follows `$10`, following and exploiting tie at the message-observed
red input** (any prior): the exploiting worlds that meet `[Π̈ = r₀]_{−red}` are the pill worlds,
where the exploit is overridden, so both sides score `5/8`.
Source: mandate T3(b); T7(d) (the deviation conditional lives on other worlds)
Kind: P
Fidelity: exact (computed for `Wnt`; the same tie holds under `Wfi`)
Hyps: none -/
theorem follows_tie_nt :
    condExpJunk (S Wnt).μ.w (S Wnt).U ((S Wnt).evS 1 1 (0, 0) ∩ (S Wnt).evFollowsMinus r₀ 1) (-1) =
      condExpJunk (S Wnt).μ.w (S Wnt).U ((S Wnt).evS 1 1 (0, 1) ∩ (S Wnt).evFollowsMinus r₀ 1) (-1) := by
  refine condExpJunk_natDiv_eq Wnt u (by norm_num) ?_ ?_ ?_ (-1)
  · rw [evS_eq, evFollowsMinus_eq]; decide +kernel
  · rw [evS_eq, evFollowsMinus_eq]; decide +kernel
  · rw [evS_eq, evS_eq, evFollowsMinus_eq]; decide +kernel

/-- **The recommendation is not stable in the Π-form under `Wnt`** (by the tie).
Source: [[communication-trust-translated]] lines 491–495; mandate T3(b)
Kind: P
Fidelity: exact
Hyps: none -/
theorem not_stable_nt : ¬ (S Wnt).Stable r₀ := by
  intro h
  have := h 1 0 (by decide) 1 (by rw [projOH_eq]; decide +kernel) 0 1 (by decide)
  exact lt_irrefl _ (follows_tie_nt ▸ this)

/-- **Advice-Following's conclusion fails at the message-observed red input under `Wnt`**:
`E[U ∣ Π*(msg, red) = $10] < E[U ∣ Π*(msg, red) = $20]` — the recommended action is strictly
worse than the deviation, so `adviceFollowing_R`'s hypothesis `StableR` is not redundant.
Source: mandate T3(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem advice_fails_nt : (S Wnt).score 1 1 (0, 0) < (S Wnt).score 1 1 (0, 1) := by
  refine score_lt_of_cnt Wnt (evS_msg_nonempty Wnt 1 (by decide) 0)
    (evS_msg_nonempty Wnt 1 (by decide) 1) ?_
  rw [evS_eq, evS_eq]
  decide +kernel

/-- **Under `Wnt` the message beats the pill at the pre input** (`E[U ∣ pill] < E[U ∣ message]`):
believing the copy follows while one exploits makes the message attractive — no flight to the
pill (findings F-5).
Source: mandate T3(c) (the expected inequality reversed under this prior)
Kind: P
Fidelity: exact (computed)
Hyps: none -/
theorem msg_beats_pill_nt (o : Fin 2) : (S Wnt).score o 0 (0, 0) < (S Wnt).score o 0 (0, 1) := by
  refine score_lt_of_cnt Wnt (evS_pre_nonempty Wnt o 0) (evS_pre_nonempty Wnt o 1) ?_
  rw [evS_eq, evS_eq]
  revert o
  decide +kernel

/-! ### T3(c): under functional identity the pill wins and the recommendation is stable -/

/-- **Under `Wfi` the pill beats the message at the pre input**: the exploiting policies
(weighted `3 : 1`) ruin the message when the copy exploits too, while the pill forces `$10` at
both rooms.
Source: [[communication-trust-translated]] line 173 ("UDT may still need to use the pill"); mandate T3(c)
Kind: P
Fidelity: exact (computed)
Hyps: none -/
theorem pill_beats_msg_fi (o : Fin 2) : (S Wfi).score o 0 (0, 1) < (S Wfi).score o 0 (0, 0) := by
  refine score_lt_of_cnt Wfi (evS_pre_nonempty Wfi o 1) (evS_pre_nonempty Wfi o 0) ?_
  rw [evS_eq, evS_eq]
  revert o
  decide +kernel

/-- **The repaired Self-Trust conclusion fails at the pre input under `Wfi`**: the pill is the
unique argmax and is not minimally modifying (while `P(Π̈ = R) < 1`, so the theorem does not
apply — its third hypothesis is what the Third Button breaks).
Source: mandate T3(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_minMod_argmax_fi (o : Fin 2) :
    ¬ ∃ a, (S Wfi).MinMod o 0 a ∧ IsArgmax ((S Wfi).score o 0) a := by
  rintro ⟨⟨ai, x⟩, hmm, harg⟩
  have : ai = 0 := Subsingleton.elim _ _
  subst this
  rcases fin2_cases x with rfl | rfl
  · exact (not_minMod_pill Wfi o).1 hmm
  · exact absurd (harg (0, 0)) (not_le.2 (pill_beats_msg_fi o))

/-- Supporting lemma: told-form stability's strict inequality at both rooms under `Wfi`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem told_follow_gt_fi : ∀ e : Fin 3, e ≠ 0 →
    condExpJunk (S Wfi).μ.w (S Wfi).U ((S Wfi).evS 1 e (0, 1) ∩ (S Wfi).evToldMinus r₀ e) (-1) <
      condExpJunk (S Wfi).μ.w (S Wfi).U ((S Wfi).evS 1 e (0, 0) ∩ (S Wfi).evToldMinus r₀ e) (-1) := by
  intro e he
  refine condExpJunk_natDiv_lt Wfi u (by norm_num) ?_ ?_ ?_ (-1)
  · rw [evS_eq, evToldMinus_eq]; revert e; decide +kernel
  · rw [evS_eq, evToldMinus_eq]; revert e; decide +kernel
  · rw [evS_eq, evS_eq, evToldMinus_eq]; revert e; decide +kernel

/-- **Under `Wfi` the recommendation "`$10` at both rooms" is stable in the told form**: given
the other room was told `$10`, following scores `5/8` and exploiting `1/4`, because the copy
exploits along with the agent. So under functional identity the source's instability does not
arise: "this would lead both copies to choose `$20`" is what UDT already prices in.
Source: [[communication-trust-translated]] lines 173, 491–495; [[examples-revisited]] Example 3; mandate T3(b), T3(c)
Kind: P
Fidelity: exact (a finding, F-5)
Hyps: none -/
theorem stableR_fi : (S Wfi).StableR r₀ := by
  intro e a₀ hr o ho ai a' ha'
  have hai : ai = 0 := Subsingleton.elim _ _
  subst hai
  rw [projOH_eq] at ho
  have ho' : sfun e o = some a₀ := ho
  clear ho
  obtain ⟨he, rfl, rfl⟩ := stableR_key e a₀ o hr ho'
  have ha'' : a' = 1 := by
    rcases fin2_cases a' with rfl | rfl
    · exact absurd rfl ha'
    · rfl
  subst ha''
  exact told_follow_gt_fi e he
where
  stableR_key : ∀ (e : Fin 3) (a₀ : Fin 2) (o : Fin 2), r₀ e = some a₀ → sfun e o = some a₀ →
      e ≠ 0 ∧ a₀ = 0 ∧ o = 1 := by decide

end TB

end Cleanroom.Udt.UdtCtExamples
