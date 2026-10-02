import Cleanroom.Trust.LegitFiniteDefect.Defs

/-!
# `legit-li-register` · Tiling: gate-tiling in a two-stage finite frame (Target 7)

trust-lab-073 / scout-fresh-eyes Q7: does a legitimacy gate starve itself of its own
justification? A finite two-stage frame, all numbers exact rationals, Mathlib and the finite
defect only (no FAF).

**The frame, declared.** Worlds `W = Corrupt × Θ × Noise` on `Fin 2`, written `(c, θ, ν)`. The
prior `π₀` is uniform (`1/8` each). The feedback channel is the **payload** `Y = θ` when the
feedback is clean (`c = 0`) and `Y = ν` (pure noise) when corrupt (`c = 1`); the corruption
evidence is `c` itself. The **gate** `g = 𝟙[c = 0]` is a function of the observable `c`: the
gated process uses the payload where the gate is open and falls back to its current mean of `θ`
where it is closed (`gatedReport π`); the ungated process takes the payload at face value
(`ungatedReport`). **The endorsement family**, declared loudly: the three indicator weights on the
payload observable, `{𝟙, 𝟙[Y = 1], 𝟙[Y = 0]}`; "endorses the gate at belief `π`" means the gated
report's finite defect is `0` on all three (`EndorsesGate π`). **The stage-1 belief** is `π₀`
**conditioned** on the admitted item, the payload `Y = 1` — and *not* on the corruption evidence
`c`, which the gate filters out of the belief (it is used only as the gate's switch): this is the
"filters exactly the evidence bearing on Corrupt" of the source (`prior1 := cond prior0 (Y = 1)`).

* **(i) Instability witness** (`stage0_endorses`, `stage0_ungated_fails`, `corrupt_frozen`,
  `stage1_not_endorses`): at `π₀` the gated report is calibrated on the family (three zeros) while
  the ungated report is not (`−1/8` on `𝟙[Y = 1]`); after the gated update the posterior on
  `Corrupt` is **frozen at the prior** (`1/2 = 1/2`), and at `π₁` the gated report's defect on `𝟙`
  is `−1/8`: stage 1 no longer endorses the gate. Mechanism: the update through the payload alone
  correlates `θ` with `c` (under `π₁`, `θ = 1` surely on the clean worlds but only half the time on
  the corrupt ones), and the gated process's fallback — its current mean of `θ` — is now the wrong
  number on exactly the worlds where it is used; the belief that would correct it is the one the
  gate filtered.
* **(ii) Transparency near-miss** (`transparency_clean_endorses`, `transparency_corrupt_endorses`):
  with the corruption evidence always conditioned on (only the payload filtered), both stage-1
  beliefs — `π₀` given `(Y = 1, c = 0)` and `π₀` given `c = 1` — endorse the gate. So the
  instability's cause is filtering the justifier, not gating as such.
* **(iii)** The tiling reading (the sober addict must keep seeing the drug's existence) is
  INTERPRETATION — findings.

All identities are by `simp`/`norm_num` over the eight worlds (`Fin.sum_univ_two`); no `decide`.
The endorsement family is three weights, not one, so the identities are not trivial; whether a
different family or a Jeffrey update changes the verdict is not examined (report, "Not done").
-/

namespace Cleanroom.Trust.LegitLiRegister.Tiling

open Cleanroom.Trust.LegitFiniteDefect Cleanroom.Found.LitDdbFrames

noncomputable section

/-- The eight worlds `(c, θ, ν)`.
Source: scout-fresh-eyes Q7 (worlds `Corrupt × Evidence × Θ`; here the evidence is `c` itself and the third coordinate is the corrupt channel's noise)
Kind: D
Fidelity: variant: the evidence coordinate is the corruption flag; a noise coordinate for the corrupt payload
Hyps: n/a -/
abbrev W3 := Fin 2 × Fin 2 × Fin 2

/-- The corruption indicator `𝟙[c = 1]`.
Source: scout-fresh-eyes Q7
Kind: D
Fidelity: exact -/
def corruptInd (w : W3) : ℝ := if w.1 = 0 then 0 else 1

/-- The target `θ` as a real.
Source: scout-fresh-eyes Q7
Kind: D
Fidelity: exact -/
def target (w : W3) : ℝ := if w.2.1 = 0 then 0 else 1

/-- The corrupt channel's noise `ν` as a real.
Source: scout-fresh-eyes Q7 (the feedback channel as a function of Evidence and Corrupt)
Kind: D
Fidelity: exact -/
def noise (w : W3) : ℝ := if w.2.2 = 0 then 0 else 1

/-- The payload: the target when clean, the noise when corrupt.
Source: scout-fresh-eyes Q7 (the feedback channel `Y`)
Kind: D
Fidelity: exact -/
def payload (w : W3) : ℝ := if w.1 = 0 then target w else noise w

/-- The uniform prior.
Source: scout-fresh-eyes Q7
Kind: D
Fidelity: exact -/
def prior0 : W3 → ℝ := fun _ => 1 / 8

/-- The gated process's report at belief `π`: the payload where the gate `𝟙[c = 0]` is open, the
belief's current mean of the target where it is closed.
Source: scout-fresh-eyes Q7 (the gated process)
Kind: D
Fidelity: variant: fallback to the current mean where gated out (declared)
Hyps: n/a -/
def gatedReport (π : W3 → ℝ) (w : W3) : ℝ := if w.1 = 0 then payload w else E π target

/-- The ungated process's report: the payload at face value.
Source: scout-fresh-eyes Q7 (not gating)
Kind: D
Fidelity: exact -/
def ungatedReport (w : W3) : ℝ := payload w

/-- The indicator weight `𝟙[Y = b]` on the payload observable.
Source: scout-fresh-eyes Q7 (indicator weights on observables)
Kind: D
Fidelity: exact -/
def indPayload (b : ℝ) (w : W3) : ℝ := if payload w = b then 1 else 0

/-- **Endorsement of the gate at belief `π`**: the gated report's finite defect is `0` on the three
declared weights `𝟙`, `𝟙[Y = 1]`, `𝟙[Y = 0]`.
Source: scout-fresh-eyes Q7 ("the finite defect-zero condition over the declared finite weight family")
Kind: D
Fidelity: exact (family declared)
Hyps: n/a -/
def EndorsesGate (π : W3 → ℝ) : Prop :=
  defect π target (gatedReport π) (fun _ => 1) = 0 ∧
    defect π target (gatedReport π) (indPayload 1) = 0 ∧
    defect π target (gatedReport π) (indPayload 0) = 0

/-- Conditioning a finite belief on an event (zero outside, renormalized inside).
Source: scout-fresh-eyes Q7 ("conditioning where `g = 1`"; declared: conditioning, not Jeffrey)
Kind: D
Fidelity: exact -/
def cond (π : W3 → ℝ) (A : W3 → Prop) [DecidablePred A] (w : W3) : ℝ :=
  if A w then π w / (∑ v, if A v then π v else 0) else 0

/-- The stage-1 belief of the gated process: `π₀` conditioned on the admitted payload `Y = 1`
(the corruption evidence is **not** conditioned on).
Source: scout-fresh-eyes Q7 (i)
Kind: D
Fidelity: exact -/
def prior1 : W3 → ℝ := cond prior0 (fun w => payload w = 1)

/-- The transparent stage-1 belief, clean branch: `π₀` conditioned on `Y = 1` **and** `c = 0`.
Source: scout-fresh-eyes Q7 (ii)
Kind: D
Fidelity: exact -/
def prior1T : W3 → ℝ := cond prior0 (fun w => payload w = 1 ∧ w.1 = 0)

/-- The transparent stage-1 belief, corrupt branch: `π₀` conditioned on `c = 1` (payload
filtered, evidence kept).
Source: scout-fresh-eyes Q7 (ii)
Kind: D
Fidelity: exact -/
def prior1T' : W3 → ℝ := cond prior0 (fun w => w.1 = 1)

/-! ## (i) The instability witness -/

/-- **Stage 0 endorses the gate**: three exact zeros.
Source: scout-fresh-eyes Q7 (i); trust-lab-073
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem stage0_endorses : EndorsesGate prior0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [defect, E, gatedReport, indPayload, payload, target, noise, prior0,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

/-- **Stage 0 does not endorse not-gating**: the ungated report's defect on `𝟙[Y = 1]` is `−1/8`.
Source: scout-fresh-eyes Q7 (i) ("ungated defect ≠ 0")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem stage0_ungated_fails :
    defect prior0 target ungatedReport (indPayload 1) = -1 / 8 := by
  simp only [defect, E, ungatedReport, indPayload, payload, target, noise, prior0,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- **The posterior on `Corrupt` is frozen at the prior** after the gated update: `1/2` before and
after.
Source: scout-fresh-eyes Q7 (i) ("`π₁`'s posterior on `Corrupt` is frozen at the prior")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem corrupt_frozen : E prior1 corruptInd = 1 / 2 ∧ E prior0 corruptInd = 1 / 2 := by
  constructor <;>
  · simp only [E, prior1, cond, corruptInd, payload, target, noise, prior0,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

/-- **Stage 1 no longer endorses the gate**: at `π₁` the gated report's defect on `𝟙` is `−1/8`.
Source: scout-fresh-eyes Q7 (i) ("stage-1 no longer endorses the gate for stage 2")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem stage1_gated_defect : defect prior1 target (gatedReport prior1) (fun _ => 1) = -1 / 8 := by
  simp only [defect, E, gatedReport, prior1, cond, payload, target, noise, prior0,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

/-- **Gate-endorsement is not preserved by the gated update** (the instability witness, headline).
Source: scout-fresh-eyes Q7 (i); trust-lab-073
Kind: P
Fidelity: exact (one frame, declared family, conditioning update)
Hyps: (a) none -/
theorem stage1_not_endorses : ¬ EndorsesGate prior1 := by
  intro h
  have := stage1_gated_defect
  rw [h.1] at this
  norm_num at this

/-! ## (ii) The transparency near-miss -/

/-- **Transparency restores endorsement, clean branch**: conditioning on `(Y = 1, c = 0)`.
Source: scout-fresh-eyes Q7 (ii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem transparency_clean_endorses : EndorsesGate prior1T := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [defect, E, gatedReport, indPayload, prior1T, cond, payload, target, noise, prior0,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

/-- **Transparency restores endorsement, corrupt branch**: conditioning on `c = 1` (payload
filtered).
Source: scout-fresh-eyes Q7 (ii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem transparency_corrupt_endorses : EndorsesGate prior1T' := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [defect, E, gatedReport, indPayload, prior1T', cond, payload, target, noise, prior0,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

/-! ## (iv) The instability is a property of the declared fallback (audit round 1, incorporated)

The gated report's fallback on the gated-out worlds is the belief's **unconditional** mean of the
target. Under `prior1` the target is correlated with `c` (`θ = 1` surely on the clean worlds, half
the time on the corrupt ones), so `E prior1 target = 3/4` is the wrong number on exactly the worlds
where it is used — that is the whole of `stage1_gated_defect = −1/8`. With the fallback read off
the belief's mean of the target **given the gate is closed**, everything else verbatim, endorsement
*is* preserved by the gated update. The posterior on `Corrupt` is frozen at `½` under both
fallbacks (`corrupt_frozen`), so the source's causal story — the gate filters the evidence bearing
on Corrupt, *so* the posterior is frozen, *so* stage 1 no longer endorses — is not what breaks
endorsement in this frame (findings F8). Probe by the round-1 adversarial auditor
(`audit-r1-probes/TilingFallback.lean`), incorporated. -/

/-- The gated report with the conditional-mean fallback: the payload where the gate is open, the
belief's mean of the target **given the gate is closed** where it is closed.
Source: audit round 1 (adversarial) N1; scout-fresh-eyes Q7 (the gated process, alternative fallback)
Kind: D
Fidelity: variant: fallback to the conditional mean where gated out (declared)
Hyps: n/a -/
def gatedReportCond (π : W3 → ℝ) (w : W3) : ℝ :=
  if w.1 = 0 then payload w else E (cond π (fun v => v.1 = 1)) target

/-- Endorsement of the conditional-fallback gate on the same three weights.
Source: audit round 1 (adversarial) N1
Kind: D
Fidelity: exact (family declared)
Hyps: n/a -/
def EndorsesGateCond (π : W3 → ℝ) : Prop :=
  defect π target (gatedReportCond π) (fun _ => 1) = 0 ∧
    defect π target (gatedReportCond π) (indPayload 1) = 0 ∧
    defect π target (gatedReportCond π) (indPayload 0) = 0

/-- Stage 0 endorses the conditional-fallback gate (three zeros, as for the declared fallback).
Source: audit round 1 (adversarial) N1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem stage0_endorses_cond : EndorsesGateCond prior0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [defect, E, gatedReportCond, cond, indPayload, payload, target, noise, prior0,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

/-- **Stage 1 endorses the conditional-fallback gate** (three zeros): with the fallback read off
the belief's conditional mean, endorsement is preserved by the gated update — the instability
witness (i) is a fact about the unconditional-mean fallback.
Source: audit round 1 (adversarial) N1; against scout-fresh-eyes Q7 (i)'s mechanism sentence
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem stage1_endorses_cond : EndorsesGateCond prior1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [defect, E, gatedReportCond, prior1, cond, indPayload, payload, target, noise,
      prior0, Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

/-- Under `prior1` the unconditional mean of the target is `3/4` while its mean given `c = 1` is
`½`: the two fallbacks differ exactly on the worlds where they are used.
Source: audit round 1 (adversarial) N1
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fallbacks_differ :
    E prior1 target = 3 / 4 ∧ E (cond prior1 (fun v => v.1 = 1)) target = 1 / 2 := by
  constructor <;>
  · simp only [E, prior1, cond, payload, target, noise, prior0,
      Fintype.sum_prod_type, Fin.sum_univ_two]
    norm_num

end

end Cleanroom.Trust.LegitLiRegister.Tiling
