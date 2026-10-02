import Cleanroom.Deference.DefSelfTrust.Witness

/-!
# Audit probe (def-self-trust, round 3, adversarial): `theoremB_perDay`'s only offered inhabitant class is vacuous on the shipped source

`theoremB_perDay` (`RobustSelfTrust.lean`, repair round 2) is the source's per-day display of
Theorem B and needs the forecast `c` P-generable. The ledger row says it is "inhabited at any
constant `c` (`PGenerableRat.ofMachineRatCodes (MachineRatCodes.const _)`), N−", with no Lean
instance in the package (the parity-tracking forecast has no P-generability certificate).

This file (i) checks that the claimed instantiation route typechecks
(`perDay_const_instance`: the constant forecast `1/2` on the parity source over `𝗣𝗔` at
`succDeferral`, `t = 2/5`, `δ = 1/20` — Prop 6.3's data), and (ii) re-derives the **exact
statement** of that instance without `theoremB_perDay`, `theoremB`, Lemma B or `est`
(`perDay_const_instance_vacuous`): the gate `Ind_{1/20}(1/2 > 2/5)` is `1`, the residual quote
is `1` eventually in every world (the deferred price of the parity family is `1/4` away from
`1/2` on all large days), so `(7/5)·E_n(⌜e_n⌝) → 7/5` dominates `E_n(X_n) − 2/5 ≥ −2/5` and
the sum is eventually `≥ 4/5 > 0`. So the constant-forecast inhabitant of `theoremB_perDay` on
the one source the package ships is the same vacuous `e ≡ 1` regime as
`theoremB_parity_instance`; the N− grade is right, and the ledger cell should say "vacuous on
the parity source" as the `theoremB_parity_instance` cells do. The three helper lemmas are
copied from the round-2 probe `TheoremBParityVacuous.lean` (probes are not importable).
Not imported by the library.
-/

namespace Cleanroom.AuditProbe.DefSelfTrust.PerDayConstantVacuous

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefSelfTrust
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- Along the deferral the price of the refutable member is eventually below `1/4`
(`thm:provind`; copied from the round-2 probe). -/
theorem deferred_price_contra_eventually_quarter (f : DeferralFunction)
    (hinj : Function.Injective f.f) :
    ∀ᶠ n in atTop, liaHistory (paperDP T) (f n) (contraAtom n) < (1 / 4 : ℝ) := by
  have h := lic_provind_false (liaHistory (paperDP T)) (paperDP T)
    (fun m => contraAtom (deferralPreimage f m))
    (contraAtom_codes.comp (unaryRuler_deferralPreimage f))
    (fun m v _ => holds_neg_contraAtom v _) (paperDP_hworld T)
  have h' : Tendsto (fun m => liaHistory (paperDP T) m (contraAtom (deferralPreimage f m)) - 0)
      atTop (𝓝 0) := h
  have hev : ∀ᶠ m in atTop,
      liaHistory (paperDP T) m (contraAtom (deferralPreimage f m)) < (1 / 4 : ℝ) := by
    filter_upwards [h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with m h1
    linarith
  have hf : Tendsto f.f atTop atTop := f.tendsto_atTop
  filter_upwards [hf.eventually hev] with n hn
  rwa [deferralPreimage_at f hinj] at hn

/-- The truncated error of the constant-`1/2` forecast on the parity source is valued `1` in
every completed-theory world, eventually (copied from the round-2 probe). -/
theorem parity_truncError_eventually_one (f : DeferralFunction) (hinj : Function.Injective f.f) :
    ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt ((truncError T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
        (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20)).luv n) 1 := by
  filter_upwards [deferred_price_taut_eventually T f hinj,
    deferred_price_contra_eventually_quarter T f hinj] with n h1 h2 v hv
  have h := truncError_reflected T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
    (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20) n v hv
  convert h using 1
  simp only [literalIndicator_expect]
  push_cast
  symm
  rw [min_eq_left]
  rw [le_div_iff₀ (by norm_num)]
  by_cases hpar : n % 2 = 0
  · rw [show parityFamily n = tautAtom n from if_pos hpar]
    have : (1 / 4 : ℝ) ≤ |(1 / 2 : ℝ) - liaHistory (paperDP T) (f n) (tautAtom n)| := by
      rw [abs_sub_comm]
      exact le_trans (by linarith) (le_abs_self _)
    norm_num
    linarith
  · rw [show parityFamily n = contraAtom n from if_neg hpar]
    have : (1 / 4 : ℝ) ≤ |(1 / 2 : ℝ) - liaHistory (paperDP T) (f n) (contraAtom n)| :=
      le_trans (by linarith) (le_abs_self _)
    norm_num
    linarith

/-- The residual's expectation is `≳ₙ 1` at the constant-`1/2` forecast on the parity source
(one eventual `thm:expprovind`; copied from the round-2 probe). -/
theorem parity_truncError_expect_asympGE_one (f : DeferralFunction)
    (hinj : Function.Injective f.f) :
    (fun n => ((truncError T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
        (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
          (liaHistory (paperDP T)) n) ≳ₙ (fun _ => (1 : ℝ)) := by
  set E := (truncError T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
    (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20)).luv with hE
  set terms : List (ℚ × (ℕ → LUV)) := [(1, E)] with hterms
  have hcodes : ∀ p ∈ terms, LUV.MachineThresholdCodeSeq p.2 := by
    intro p hp
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact (truncError T f (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
      (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20)).poly
  have hbdd : ∀ n, (constComb (-1) terms n).l1Norm (liaHistory (paperDP T)) ≤ 2 := fun n => by
    norm_num [constComb_l1Norm, hterms]
  have hwv : LUVCombination.WorldValued (constComb (-1) terms) (paperDP T) := fun n v hv => by
    refine ⟨worldValue v, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := mem_constComb_terms hp
    rw [hpq]
    simp only [hterms, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact valuesAt_worldValue (truncError_reflected T f
      (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
      (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20) n v hv)
  have hval : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      ∀ ν, (constComb (-1) terms n).ValuesAt v ν →
        (0 : ℝ) ≤ (constComb (-1) terms n).value (liaHistory (paperDP T)) ν := by
    filter_upwards [parity_truncError_eventually_one T f hinj] with n hn v hv ν hν
    have e := (hν (EF.const 1, E n) (by simp [constComb, hterms])).eq (hn v hv)
    rw [constComb_value]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e]
    push_cast
    linarith
  have h := expect_asympGE_of_eventually (constCombSyntax (-1) terms hcodes) hbdd hwv
    (c := 0) le_rfl hval (paperDP_hworld T)
  have hEq : (fun n => (constComb (-1) terms n).expect (liaHistory (paperDP T)) n) =
      (fun n => (E n).expect (liaHistory (paperDP T)) n - 1) := by
    funext n
    rw [constComb_expect]
    simp only [hterms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rw [hEq] at h
  intro ε hε
  filter_upwards [h ε hε] with n hn
  try simp only at hn ⊢
  linarith

end

/-- The constant forecast `1/2` is P-generable by the route the ledger names. -/
theorem constHalf_pgenerable :
    PGenerableRat (liaHistory (paperDP 𝗣𝗔)) (fun _ : ℕ => (1 / 2 : ℚ)) :=
  PGenerableRat.ofMachineRatCodes (MachineRatCodes.const _) _

/-- **(i) The ledger's instantiation route typechecks**: `theoremB_perDay` at the constant
forecast `1/2` on the parity source over `𝗣𝗔` at `succDeferral`, `t = 2/5`, `δ = 1/20`. -/
theorem perDay_const_instance :
    (fun n => ctsInd (1 / 20 : ℚ) (((1 / 2 : ℚ)) : ℝ) ((2 / 5 : ℚ) : ℝ) *
          ((literalIndicator (parityFamily n)).expect (liaHistory (paperDP 𝗣𝗔)) n -
            ((2 / 5 : ℚ) : ℝ)) +
        (1 + ((2 / 5 : ℚ) : ℝ)) *
          ((truncError 𝗣𝗔 succDeferral (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
            (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
            (liaHistory (paperDP 𝗣𝗔)) n) ≳ₙ (fun _ => (0 : ℝ)) :=
  theoremB_perDay 𝗣𝗔 succDeferral succDeferral_injective
    (literalIndicator_machineThresholdCodeSeq parityFamily_codes) (paritySource_valued 𝗣𝗔)
    constHalf_pgenerable (by norm_num : (0 : ℚ) < 1 / 20) (by norm_num : (0 : ℚ) ≤ 2 / 5)

/-- **(ii) The exact statement of `perDay_const_instance`, without `theoremB_perDay`,
`theoremB`, Lemma B or `est`**: gate `1`, residual expectation `≳ₙ 1`, source expectation
`≥ 0`, so the sum is eventually `≥ −2/5 + (7/5)(6/7) = 4/5`. -/
theorem perDay_const_instance_vacuous :
    (fun n => ctsInd (1 / 20 : ℚ) (((1 / 2 : ℚ)) : ℝ) ((2 / 5 : ℚ) : ℝ) *
          ((literalIndicator (parityFamily n)).expect (liaHistory (paperDP 𝗣𝗔)) n -
            ((2 / 5 : ℚ) : ℝ)) +
        (1 + ((2 / 5 : ℚ) : ℝ)) *
          ((truncError 𝗣𝗔 succDeferral (literalIndicator_machineThresholdCodeSeq parityFamily_codes)
            (Computable.const (1 / 2 : ℚ)) (by norm_num : (0 : ℚ) < 1 / 20)).luv n).expect
            (liaHistory (paperDP 𝗣𝗔)) n) ≳ₙ (fun _ => (0 : ℝ)) := by
  have hgate : ctsInd (1 / 20 : ℚ) (((1 / 2 : ℚ)) : ℝ) ((2 / 5 : ℚ) : ℝ) = 1 := by
    rw [ctsInd_eq_one_iff (by norm_num)]
    norm_num
  have hres := parity_truncError_expect_asympGE_one 𝗣𝗔 succDeferral succDeferral_injective
  intro ε hε
  filter_upwards [hres (1 / 7) (by norm_num)] with n hn
  have hX := LUV.expect_mem_Icc (liaHistory (paperDP 𝗣𝗔)) n (literalIndicator (parityFamily n))
    (fun s => liaHistory_range (paperDP 𝗣𝗔) n s)
  try simp only at hn ⊢
  rw [hgate]
  push_cast at hn hX ⊢
  linarith [hX.1]

end Cleanroom.AuditProbe.DefSelfTrust.PerDayConstantVacuous
