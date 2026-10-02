import Cleanroom.Decision.DpCausalConsist.TbTheta

/-!
# `dp-causal-consist`: the stay-label N− — Axiom NR does not pin NR-cf(cross) on `TB(θ)` (T8, finding F4)

At the stay label `q = 0` of `TB(θ)` the `¬bot` cell is positive but meets `cross` with
probability `0` (`tb_stay_guard_fails`). Here a family of counterfactual components `cfNR v`,
one per fill value `v`, is shown to satisfy Axiom NR with `exo := bot` for **every** `v`
(`cfNR_nrAt`), while

* its supposition of `cross` gives the positive-mass event `{(¬bot, cross)}` probability `1 − θ`
  where the K-partition state gives it `0` (`cfNR_ne_kPart`: the N− companion of
  `nr_forces_kpart` — without the guard, `NRAt` does not force `kPart`);
* its NR-cf(cross) is `−10θ + (1 − θ)·v` (`cfNR_value`): `v = 10` reproduces the note's
  `10 − 20θ`, `v = 0` gives `−10θ`. The axiom pins the law of `cf(cross)` on this four-point
  space (success + clause (i)) but not its desirability at the `P_s`-null world `(¬bot, cross)`,
  where clause (iii) is silent.

The components are built from a two-point law and a utility (`stateOfU`, the ℚ-twin of
`expState`); `cf` on events other than the two act events is a point mass (any state with
success will do; NR reads only the act events).
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Finset

section stateOfU

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The state with law `P` and desirability `𝔼_P[u | X]`, over `ℚ` (the twin of `expState`).
Source: none: infrastructure
Kind: D -/
def stateOfU (P : FinDistr ℚ Ω) (u : Ω → ℚ) : State Ω ℚ where
  P := P
  V X := (∑ ω ∈ X, P.w ω * u ω) / probOf P X
  avg X Y h hX hY := by
    simp only [probOf] at hX hY ⊢
    rw [Finset.sum_union h, Finset.sum_union h]
    have hsum : 0 < ∑ x ∈ X, P.w x + ∑ x ∈ Y, P.w x := by linarith
    field_simp

/-- `P` of `stateOfU`. Source: none: infrastructure. Kind: L -/
theorem stateOfU_pr (P : FinDistr ℚ Ω) (u : Ω → ℚ) (X : Finset Ω) :
    (stateOfU P u).pr X = probOf P X := rfl

/-- `V` of `stateOfU`. Source: none: infrastructure. Kind: L -/
theorem stateOfU_V (P : FinDistr ℚ Ω) (u : Ω → ℚ) (X : Finset Ω) :
    (stateOfU P u).V X = (∑ ω ∈ X, P.w ω * u ω) / probOf P X := rfl

/-- The two-point law `θ δ_{ω₁} + (1 − θ) δ_{ω₂}`. Source: none: infrastructure. Kind: D -/
def twoPt (ω₁ ω₂ : Ω) (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : FinDistr ℚ Ω where
  w ω := (if ω = ω₁ then θ else 0) + (if ω = ω₂ then 1 - θ else 0)
  nonneg ω := by split_ifs <;> linarith
  sum_one := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp

/-- `probOf` of the two-point law. Source: none: infrastructure. Kind: L -/
theorem probOf_twoPt (ω₁ ω₂ : Ω) (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (X : Finset Ω) :
    probOf (twoPt ω₁ ω₂ θ h0 h1) X = (if ω₁ ∈ X then θ else 0) + (if ω₂ ∈ X then 1 - θ else 0) := by
  unfold probOf twoPt
  simp only
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- Sums against the two-point law. Source: none: infrastructure. Kind: L -/
theorem sum_twoPt_mul (ω₁ ω₂ : Ω) (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (X : Finset Ω) (f : Ω → ℚ) :
    ∑ ω ∈ X, (twoPt ω₁ ω₂ θ h0 h1).w ω * f ω
      = (if ω₁ ∈ X then θ * f ω₁ else 0) + (if ω₂ ∈ X then (1 - θ) * f ω₂ else 0) := by
  unfold twoPt
  simp only
  simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq']

end stateOfU

section nrWitness

variable (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)

/-- The fill utility: `−10` at `(bot, cross)`, `v` at `(¬bot, cross)`, `0` on `stay`.
Source: finding F4 (the free value of `cf(cross)` at the `P_s`-null world)
Kind: D -/
def uFill (v : ℚ) : TbW → ℚ
  | (true, .a) => -10
  | (false, .a) => v
  | (_, .b) => 0

/-- The supposition of `cross`: `θ δ_{(bot,cross)} + (1−θ) δ_{(¬bot,cross)}` with utility `uFill v`.
Source: finding F4
Kind: D -/
def cfCross (v : ℚ) : State TbW ℚ :=
  stateOfU (twoPt (true, Act2.a) (false, Act2.a) θ h0 h1) (uFill v)

/-- The supposition of `stay`: `θ δ_{(bot,stay)} + (1−θ) δ_{(¬bot,stay)}`.
Source: finding F4
Kind: D -/
def cfStay (v : ℚ) : State TbW ℚ :=
  stateOfU (twoPt (true, Act2.b) (false, Act2.b) θ h0 h1) (uFill v)

/-- **A counterfactual component for `TB(θ)` at the stay label** with fill `v`: the calibrated
state `tbState θ 0` and the suppositions `cfCross v`, `cfStay v` on the two act events (a point
mass elsewhere).
Source: finding F4; mandate T8 (the N− companion)
Kind: D -/
noncomputable def cfNR (v : ℚ) : CfState TbW ℚ where
  s := tbState θ h0 h1 0 le_rfl zero_le_one
  cf A h :=
    if A = tbActEv () Act2.a then cfCross θ h0 h1 v
    else if A = tbActEv () Act2.b then cfStay θ h0 h1 v
    else State.dirac h.choose 0
  success A h := by
    split_ifs with hA hB
    · subst hA
      rw [cfCross, stateOfU_pr, probOf_twoPt]
      simp [tbActEv]
    · subst hB
      rw [cfStay, stateOfU_pr, probOf_twoPt]
      simp [tbActEv]
    · rw [State.dirac_pr, if_pos h.choose_spec]

/-- `cfNR` on the `cross` event. Source: none: infrastructure. Kind: L -/
theorem cfNR_cf_cross (v : ℚ) (h : (tbActEv () Act2.a).Nonempty) :
    (cfNR θ h0 h1 v).cf (tbActEv () Act2.a) h = cfCross θ h0 h1 v := by
  unfold cfNR
  simp

/-- `cfNR` on the `stay` event. Source: none: infrastructure. Kind: L -/
theorem cfNR_cf_stay (v : ℚ) (h : (tbActEv () Act2.b).Nonempty) :
    (cfNR θ h0 h1 v).cf (tbActEv () Act2.b) h = cfStay θ h0 h1 v := by
  unfold cfNR
  simp
  intro h'
  exact absurd h' (by decide)

/-- The calibrated state at the stay label, on an arbitrary event.
Source: none: infrastructure
Kind: L -/
theorem tbState0_pr (X : Finset TbW) :
    (tbState θ h0 h1 0 le_rfl zero_le_one).pr X
      = (if (true, Act2.a) ∈ X then θ else 0) + (if (false, Act2.b) ∈ X then 1 - θ else 0) := by
  rw [tbState_pr]; simp

/-- Its desirability on an arbitrary event. Source: none: infrastructure. Kind: L -/
theorem tbState0_V (X : Finset TbW) :
    (tbState θ h0 h1 0 le_rfl zero_le_one).V X
      = (if (true, Act2.a) ∈ X then θ * (-10) else 0)
        / ((if (true, Act2.a) ∈ X then θ else 0) + (if (false, Act2.b) ∈ X then 1 - θ else 0)) := by
  rw [tbState_V]; simp

/-- **`cfNR v` satisfies Axiom NR with `exo := bot` for every fill `v`.**
Source: [[non-responsiveness]] "Axiom NR" clauses (i)–(ii); finding F4
Kind: N−
Fidelity: exact (the stay label `q = 0`: the regime of the finding) -/
theorem cfNR_nrAt (v : ℚ) : NRAt (cfNR θ h0 h1 v) (tbActEv ()) exoBot := by
  intro a h
  have hs : ∀ X, (cfNR θ h0 h1 v).s.pr X
      = (if (true, Act2.a) ∈ X then θ else 0) + (if (false, Act2.b) ∈ X then 1 - θ else 0) :=
    tbState0_pr θ h0 h1
  have hsV : ∀ X, (cfNR θ h0 h1 v).s.V X
      = (if (true, Act2.a) ∈ X then θ * (-10) else 0)
        / ((if (true, Act2.a) ∈ X then θ else 0) + (if (false, Act2.b) ∈ X then 1 - θ else 0)) :=
    tbState0_V θ h0 h1
  cases a
  · -- cross
    rw [cfNR_cf_cross]
    refine ⟨?_, ?_, ?_⟩
    · intro e
      rw [cfCross, stateOfU_pr, probOf_twoPt, hs]
      cases e <;> simp [cell, exoBot]
    · intro e X hpos
      cases e
      · exfalso
        rw [hs] at hpos
        simp [tbActEv, cell, exoBot] at hpos
      · rw [cfCross, stateOfU_pr, stateOfU_pr, probOf_twoPt, probOf_twoPt, hs, hs]
        simp [cell, exoBot, tbActEv]
    · intro e X hpos
      cases e
      · exfalso
        rw [hs] at hpos
        simp [tbActEv, cell, exoBot] at hpos
      · have hmem : (true, Act2.a) ∈ X := by
          rw [hs] at hpos
          by_contra hc
          simp [tbActEv, cell, exoBot, hc] at hpos
        rw [cfCross, stateOfU_V, sum_twoPt_mul, probOf_twoPt, hsV]
        simp [cell, exoBot, tbActEv, hmem, uFill]
  · -- stay
    rw [cfNR_cf_stay]
    refine ⟨?_, ?_, ?_⟩
    · intro e
      rw [cfStay, stateOfU_pr, probOf_twoPt, hs]
      cases e <;> simp [cell, exoBot]
    · intro e X hpos
      cases e
      · rw [cfStay, stateOfU_pr, stateOfU_pr, probOf_twoPt, probOf_twoPt, hs, hs]
        simp [cell, exoBot, tbActEv]
      · exfalso
        rw [hs] at hpos
        simp [tbActEv, cell, exoBot] at hpos
    · intro e X hpos
      cases e
      · have hmem : (false, Act2.b) ∈ X := by
          rw [hs] at hpos
          by_contra hc
          simp [tbActEv, cell, exoBot, hc] at hpos
        rw [cfStay, stateOfU_V, sum_twoPt_mul, probOf_twoPt, hsV]
        simp [cell, exoBot, tbActEv, hmem, uFill]
      · exfalso
        rw [hs] at hpos
        simp [tbActEv, cell, exoBot] at hpos

/-- **The N− companion of `nr_forces_kpart`**: at the stay label, `cfNR v` is `NRAt` yet its
supposition of `cross` gives `{(¬bot, cross)}` probability `1 − θ > 0` while the K-partition
state gives it `0` — without the guard "every positive cell meets `a` positively", NR does not
force the K-partition law.
Source: [[non-responsiveness]] ("Hence `P^a_s = ∑_e P_s(e) P_s(· | a, e)`" — not at the stay
label); mandate T8 (the N− companion); finding F4
Kind: N− -/
theorem cfNR_ne_kPart (hθ0 : 0 < θ) (hθ1 : θ < 1) (v : ℚ) :
    NRAt (cfNR θ h0 h1 v) (tbActEv ()) exoBot ∧
    ((cfNR θ h0 h1 v).cf (tbActEv () Act2.a) ⟨(true, Act2.a), by simp [tbActEv]⟩).pr {(false, Act2.a)}
      = 1 - θ ∧
    (kPart (cfNR θ h0 h1 v).s (tbActEv () Act2.a) exoBot).pr {(false, Act2.a)} = 0 := by
  refine ⟨cfNR_nrAt θ h0 h1 v, ?_, ?_⟩
  · rw [cfNR_cf_cross, cfCross, stateOfU_pr, probOf_twoPt]
    simp
  · rw [kPart_pr, Fintype.sum_bool]
    have hs : ∀ X, (cfNR θ h0 h1 v).s.pr X
        = (if (true, Act2.a) ∈ X then θ else 0) + (if (false, Act2.b) ∈ X then 1 - θ else 0) :=
      tbState0_pr θ h0 h1
    have hbad : ¬ 0 < (cfNR θ h0 h1 v).s.pr (tbActEv () Act2.a ∩ cell exoBot false) := by
      rw [hs]; simp [tbActEv, cell, exoBot]
    have hF : 0 < (cfNR θ h0 h1 v).s.pr (cell exoBot false) := by
      rw [hs]; simp [cell, exoBot]; linarith
    have hT : 0 < (cfNR θ h0 h1 v).s.pr (tbActEv () Act2.a ∩ cell exoBot true) := by
      rw [hs]; simp [tbActEv, cell, exoBot]; exact hθ0
    rw [kPartComp_pr, kPartComp_pr, if_pos hT, if_neg hbad, if_pos hF, hs, hs, hs, hs, hs]
    simp [cell, exoBot, tbActEv]

/-- **NR-cf(cross) is not determined by Axiom NR at the stay label**: `cfNR v` is `NRAt` for every
`v`, and its NR-cf(cross) is `−10θ + (1−θ)·v` — `10 − 20θ` at `v = 10` (the note's value), `−10θ`
at `v = 0`.
Source: [[non-responsiveness]] ("NR-cf(cross) `= 8`" at the stay label, `θ = 1/10`); finding F4
Kind: N− -/
theorem cfNR_value (v : ℚ) :
    ((cfNR θ h0 h1 v).cf (tbActEv () Act2.a) ⟨(true, Act2.a), by simp [tbActEv]⟩).V
      (tbActEv () Act2.a) = -10 * θ + (1 - θ) * v := by
  rw [cfNR_cf_cross, cfCross, stateOfU_V, sum_twoPt_mul, probOf_twoPt]
  simp [tbActEv, uFill]
  ring

end nrWitness

end Cleanroom.Decision.DpCausalConsist
