import Cleanroom.Deference.DefDoseResponse.Defs
import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Cleanroom.Deference.DefTrackingPin.Pin

/-!
# `def-dose-response` · Audit: the audit is exact; decided content auto-passes (T3, T3.5)

**T3** for *arbitrary* logical inductors over *arbitrary* processes and any e.c. LUV `X` whose
expectation converges on both (FAF's `expect_converges` package: `hcode`, `hcons`, `hval`) — the
note's "no twin assumption" is the quantifier over `Pi`, `Pj`, `DPi`, `DPj`:

* **(i) soundness, every battery** (`audit_sound`): if the destinations agree, the `w`-weighted
  average of the gap vanishes for *every* battery `w` (any nonnegative real weighting with
  divergent mass — the auditor is not a player, so this is not restricted to generable features);
* **(ii) completeness from the uniform weighting** (`audit_complete`): the Cesàro gap tends to the
  destination gap, so a destination gap is visible to the crudest statistic
  (`audit_complete_ne`);
* **`audit_exact`**: all batteries pass ⟺ the destinations agree, and `uniform_passes_iff`: the
  uniform audit passes ⟺ the destinations agree.

**T3.5** (`decided_content_auto_passes`): a LUV determined via the shared base at `y` is determined
via every extension of it (`determinedVia_of_stage_subset`), so every arm's destination is `y`
(`def-tracking-pin`'s `pinning_fixed_expectInf`, FAF's `thm:ec`) and every cross-arm audit on it
passes — for any inductors, any stream, any coins. This is the *derivation* of the `hi`/`hj` the
zip's `decided_content_auto_passes` assumed (zip AUDIT §3.5).

Everything here is grade (a): the only inputs are FAF's `expect_converges`, `li-asymp-calc`'s
weighted-average and Cesàro lemmas, and `def-tracking-pin`'s snapshot identity. Traps honoured:
(i) `expectInf` is `Classical.choose`d — (ii) is stated through `Tendsto` of the expectation
sequences and `L_i − L_j` is derived as the limit of the gap (`crossArmGap_tendsto`); (ii)
batteries are real sequences; (iii) `cesaro x 0 = 0` is junk, everything is `atTop`.
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefTrackingPin
open Filter Topology

section exact

variable {Pi Pj : History} {DPi DPj : DeductiveProcess} [IsLogicalInductor Pi DPi]
  [IsLogicalInductor Pj DPj] {X : LUV} (hcode : X.MachineThresholdCodes)
  (hconsi : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPi.D n))
  (hconsj : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPj.D n))
  (hvali : ∀ v : PCWorld, v.ConsistentWithTheory DPi → ∃ x : ℝ, v.ValuesAt X x)
  (hvalj : ∀ v : PCWorld, v.ConsistentWithTheory DPj → ∃ x : ℝ, v.ValuesAt X x)

/-- **The gap converges to the destination gap**: `𝔼^{(i)}_n(X) − 𝔼^{(j)}_n(X) → L_i − L_j`, from
FAF's `expect_converges` on each arm (two `Tendsto.sub`). The destinations exist by Expectations
Converge [LI 4.8.3].
Source: [[dose-response]] §7 T3 ("Limits exist by Expectations Converge [LI 4.8.3]")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem crossArmGap_tendsto :
    Tendsto (crossArmGap Pi Pj X) atTop
      (𝓝 (X.expectInf Pi DPi hcode hconsi hvali - X.expectInf Pj DPj hcode hconsj hvalj)) :=
  (X.expectSeq_convergesTo_expectInf Pi DPi hcode hconsi hvali).sub
    (X.expectSeq_convergesTo_expectInf Pj DPj hcode hconsj hvalj)

/-- **T3 (i), soundness for every battery (headline).** If the two arms' destinations on `X`
agree, every cross-arm audit on `X` passes: for *every* battery `w` (nonnegative, divergent mass)
the `w`-weighted average of the gap tends to `0`. No false alarms from any battery, ever. Arbitrary
inductors over arbitrary processes; no twin assumption.
Source: [[dose-response]] §7 T3 (i); anson-055; anson-2-030
Kind: C
Fidelity: exact (batteries are arbitrary real weightings, stronger than "divergent weighting")
Hyps: (a) none -/
theorem audit_sound
    (hL : X.expectInf Pi DPi hcode hconsi hvali = X.expectInf Pj DPj hcode hconsj hvalj) :
    ∀ w, IsBattery w → passes w Pi Pj X := by
  intro w hw
  have h := crossArmGap_tendsto (Pi := Pi) (Pj := Pj) hcode hconsi hconsj hvali hvalj
  rw [hL, sub_self] at h
  exact weightedAverage_tendsto_zero hw.1 hw.2 h

/-- **T3 (ii), completeness from the uniform weighting (headline).** The Cesàro cross-arm audit
tends to the destination gap `L_i − L_j`.
Source: [[dose-response]] §7 T3 (ii); anson-055
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem audit_complete :
    Tendsto (crossArmAudit Pi Pj X) atTop
      (𝓝 (X.expectInf Pi DPi hcode hconsi hvali - X.expectInf Pj DPj hcode hconsj hvalj)) :=
  tendsto_cesaro (crossArmGap_tendsto (Pi := Pi) (Pj := Pj) hcode hconsi hconsj hvali hvalj)

/-- **T3 (ii) in the vocabulary of D5**: the uniform Cesàro audit tends to the cross-arm effect of
record `crossArmEffect` (the definition the note's §2.5 D4 names; adversarial audit r1, N6).
Source: [[dose-response]] §2.5 D4 ("whose limit (T3) is exactly the destination gap"), §7 T3 (ii)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem audit_complete_effect :
    Tendsto (crossArmAudit Pi Pj X) atTop
      (𝓝 (crossArmEffect Pi Pj DPi DPj X hcode hconsi hconsj hvali hvalj)) :=
  audit_complete (Pi := Pi) (Pj := Pj) hcode hconsi hconsj hvali hvalj

/-- **The uniform audit passes iff the destinations agree.**
Source: [[dose-response]] §7 ("dose-invariance of destinations … is exactly the event that all uniform Cesàro audits pass")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem uniform_passes_iff :
    Tendsto (crossArmAudit Pi Pj X) atTop (𝓝 0) ↔
      X.expectInf Pi DPi hcode hconsi hvali = X.expectInf Pj DPj hcode hconsj hvalj := by
  constructor
  · intro h0
    exact sub_eq_zero.mp
      (tendsto_nhds_unique (audit_complete (Pi := Pi) (Pj := Pj) hcode hconsi hconsj hvali hvalj) h0)
  · intro hL
    have h := audit_complete (Pi := Pi) (Pj := Pj) hcode hconsi hconsj hvali hvalj
    rwa [hL, sub_self] at h

/-- **T3 (ii), the negative form**: a destination gap is never missed by the uniform statistic.
Source: [[dose-response]] §7 T3 (ii) ("a convergent statistic with nonzero limit cannot also converge to `0`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem audit_complete_ne
    (h : X.expectInf Pi DPi hcode hconsi hvali ≠ X.expectInf Pj DPj hcode hconsj hvalj) :
    ¬ Tendsto (crossArmAudit Pi Pj X) atTop (𝓝 0) :=
  fun h0 => h ((uniform_passes_iff (Pi := Pi) (Pj := Pj) hcode hconsi hconsj hvali hvalj).mp h0)

/-- **T3, `audit_exact` (headline).** All cross-arm audits on `X` pass, over every battery, iff
the two destinations agree. (⇐) is soundness; (⇒) reads the uniform battery `w ≡ 1`, whose
weighted average is the Cesàro mean shifted by one day (`cesaro_eq_weightedAverage_one`), and
uses completeness. Arbitrary inductors over arbitrary processes.
Source: [[dose-response]] §7 T3 ("Hence dose-invariance of destinations on `D_prot` is exactly the event that all uniform Cesàro audits pass"); anson-055
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem audit_exact :
    (∀ w, IsBattery w → passes w Pi Pj X) ↔
      X.expectInf Pi DPi hcode hconsi hvali = X.expectInf Pj DPj hcode hconsj hvalj := by
  constructor
  · intro h
    have h1 := h _ isBattery_one
    have h2 : Tendsto (crossArmAudit Pi Pj X) atTop (𝓝 0) := by
      rw [← tendsto_add_atTop_iff_nat 1]
      refine h1.congr fun N => ?_
      show weightedAverage (fun _ => (1 : ℝ)) (crossArmGap Pi Pj X) N =
        cesaro (crossArmGap Pi Pj X) (N + 1)
      rw [cesaro_eq_weightedAverage_one _ (Nat.le_add_left 1 N), Nat.add_sub_cancel]
    exact (uniform_passes_iff (Pi := Pi) (Pj := Pj) hcode hconsi hconsj hvali hvalj).mp h2
  · exact audit_sound (Pi := Pi) (Pj := Pj) hcode hconsi hconsj hvali hvalj

end exact

/-! ## T3.5 — decided content auto-passes -/

/-- **A LUV determined via a process is determined via every stage-wise extension of it**: a
completed-theory world of the extension is one of the base.
Source: mandate T3.5 (`determinedVia_of_stage_subset`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem determinedVia_of_stage_subset {X : LUV} {base DP : DeductiveProcess} {y : ℝ}
    (hsub : ∀ n, base.D n ⊆ DP.D n) (hdet : LUV.DeterminedVia X base y) :
    LUV.DeterminedVia X DP y :=
  fun v hv => hdet v (fun n φ hφ => hv n φ (hsub n hφ))

/-- **An arm's destination on base-decided content is the decided value**: for any inductor over
any extension of the base, `𝔼_∞(X) = y` when the base determines `X` at `y`
(`def-tracking-pin`'s `pinning_fixed_expectInf`, FAF's `thm:ec`, through
`determinedVia_of_stage_subset`).
Source: [[dose-response]] §7 Cor T3.5 ("every arm has `E^{(i)}_∞(X) = Val_{Γ_0}(X)`")
Kind: C
Fidelity: exact (FAF's `DeterminedVia` in place of "determined via `Γ_0` with its value decided")
Hyps: (a) none -/
theorem expectInf_eq_of_decided_base {X : LUV} {P : History} {base DP : DeductiveProcess}
    [IsLogicalInductor P DP] (hcode : X.MachineThresholdCodes)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (hsub : ∀ n, base.D n ⊆ DP.D n)
    {y : ℝ} (hdet : LUV.DeterminedVia X base y) :
    X.expectInf P DP hcode hcons
      (determinedVia_exists_valuesAt (determinedVia_of_stage_subset hsub hdet)) = y :=
  pinning_fixed_expectInf hcode hcons (determinedVia_of_stage_subset hsub hdet)

/-- **T3.5, `decided_content_auto_passes` (headline).** If `X` is determined via the shared base
at `y`, then for *any* two inductors over *any* extensions of the base, every cross-arm audit on
`X` passes over every battery, and the uniform audit passes — misfiling decided content into the
protected class is harmless, for any stream and any coins. The destinations `L_i = y = L_j` are
*derived* (`expectInf_eq_of_decided_base`), not assumed.
Source: [[dose-response]] §7 Cor T3.5; anson-055; anson-2-030 (the provenance upgrade of the zip's `decided_content_auto_passes`, AUDIT §3.5)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem decided_content_auto_passes {X : LUV} {Pi Pj : History} {base DPi DPj : DeductiveProcess}
    [IsLogicalInductor Pi DPi] [IsLogicalInductor Pj DPj] (hcode : X.MachineThresholdCodes)
    (hconsi : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPi.D n))
    (hconsj : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPj.D n))
    (hsubi : ∀ n, base.D n ⊆ DPi.D n) (hsubj : ∀ n, base.D n ⊆ DPj.D n)
    {y : ℝ} (hdet : LUV.DeterminedVia X base y) :
    (∀ w, IsBattery w → passes w Pi Pj X) ∧ Tendsto (crossArmAudit Pi Pj X) atTop (𝓝 0) := by
  have hi := expectInf_eq_of_decided_base (P := Pi) hcode hconsi hsubi hdet
  have hj := expectInf_eq_of_decided_base (P := Pj) hcode hconsj hsubj hdet
  exact ⟨audit_sound (Pi := Pi) (Pj := Pj) hcode hconsi hconsj _ _ (hi.trans hj.symm),
    (uniform_passes_iff (Pi := Pi) (Pj := Pj) hcode hconsi hconsj _ _).mpr (hi.trans hj.symm)⟩

/-- **T3.5 at the arms**: for any two inductors over exposure ledgers of the same base (any
coins, any streams), base-decided content auto-passes.
Source: [[dose-response]] §7 Cor T3.5 ("for any inductors and any quote policy")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem decided_content_auto_passes_arms {X : LUV} {Pi Pj : History} {base : DeductiveProcess}
    {ci cj : ℕ → Bool} {ai aj : ℕ → ℚ} [IsLogicalInductor Pi (armProcess base ci ai)]
    [IsLogicalInductor Pj (armProcess base cj aj)] (hcode : X.MachineThresholdCodes)
    (hconsi : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base ci ai).D n))
    (hconsj : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base cj aj).D n))
    {y : ℝ} (hdet : LUV.DeterminedVia X base y) :
    (∀ w, IsBattery w → passes w Pi Pj X) ∧ Tendsto (crossArmAudit Pi Pj X) atTop (𝓝 0) :=
  decided_content_auto_passes hcode hconsi hconsj (base_subset_armProcess base ci ai)
    (base_subset_armProcess base cj aj) hdet

end Cleanroom.Deference.DefDoseResponse
