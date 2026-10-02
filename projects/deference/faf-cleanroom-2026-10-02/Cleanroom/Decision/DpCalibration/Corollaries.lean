import Cleanroom.Decision.DpCalibration.Theories

/-!
# Corollaries added in repair round 1

* `maskedOCAtV_GP_vacuity_iff_nuPoly` (audit N5): the vacuity disjunct of the global-plain
  masked sense — "no procedure realizes `O_d`" — is exactly `nuPoly C B (obs d) = 0`, the limit
  sense's "unrealized". The two vocabularies of "unrealized" coincide for `GP`; for the local
  variants they do not (`fantasy241` at `d₂`: every local self-model gives `ν(O₂) = 0` although a
  chance-positive leaf has its world in `O₂`).
* **CA-12′'s consequence** (mandate T15(d), audit N3): under `RecordsForAll`, the strict act
  values at `d` are `C(d)`-independent where defined (`V_actEv_eq_of_recordsForAll`), so (i) a
  properly mixed label is strictly-calibrated-and-approved only at a tie of those values
  (`tie_of_mixed_approved`), and (ii) approval transfers to every sub-mixture at `d` — in
  particular to each pure label in the support (`tEdtAt_of_support_subset_of_recordsForAll`;
  that the sub-mixture realizes `O_d` is derived, `nu_obs_pos_of_support_subset_of_recordsForAll`,
  repair round 2): the mixed label is never forced by calibration-plus-approval.

The witnesses for these three theorems live in `TieTree.lean` (N+, the one-point tie tree) —
**not** on the miniature, which is nested and recorded by no procedure
(`miniature_not_recordsFor`, `Miniature.lean`). This file does not import the catalogue.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ## "Unrealized" in the masked (GP) and limit vocabularies -/

/-- **The GP vacuity disjunct is `nuPoly (O_d) = 0`**: no procedure realizes `O_d` iff no
chance-positive leaf has its world in `O_d` iff `O_d` is not tremble-realizable.
Source: [[decision-problems-v2]] §3.1 Definitions 9–10 (the two senses of "unrealized");
`calibration.md` Definition C1 (GP); audit round 1 N5
Kind: L
Fidelity: exact -/
theorem maskedOCAtV_GP_vacuity_iff_nuPoly [∀ d, Nonempty (acts d)] (obs : ι → Finset Ω)
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) :
    (∀ C', Admissible .GP C d C' → nu C' B (obs d) = 0) ↔ nuPoly C B (obs d) = 0 := by
  constructor
  · intro h
    by_contra hne
    have := (nuPoly_ne_zero_iff_forall_pos C B (obs d)).mp hne 1 one_pos le_rfl
    rw [h _ trivial] at this
    exact lt_irrefl _ this
  · intro h C' _
    by_contra hne
    have hex : ∃ ℓ, world B ℓ ∈ obs d ∧ 0 < chanceWeight B ℓ := by
      rw [nu_eq_sum] at hne
      obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      by_cases hw : world B ℓ ∈ obs d
      · refine ⟨ℓ, hw, ?_⟩
        rw [if_pos hw] at hℓ
        exact Positive.of_leafLaw_pos C' ((leafLaw_nonneg C' B ℓ).lt_of_ne (Ne.symm hℓ))
      · rw [if_neg hw] at hℓ; exact absurd rfl hℓ
    exact ((nuPoly_ne_zero_iff C B (obs d)).mpr hex) h

/-! ## Lemma 2's converse at realized points (repair round 2) -/

/-- **Lemma 2's converse at a realized point**: where `ν_C(O_d) > 0`, strict OC at `d` implies
limit OC at `d` — `nuPoly O_d` has order `0` with constant term `ν_C(O_d)`, so the limiting
conditional is the strict one (`limitCond_eq_of_pos`) and the `V`-clause at order `0` is strict
clause 2. With `limitOCAt_imp_strictOCAt` the two senses coincide at every realized point
(`limitOCAt_iff_strictOCAt_of_pos`); Lemma 2's converse fails only off "realized" (T3(b),
`tys_take5_strict_not_limit`, where `ν_C(O₁₀) = 0`). Used by `LimitTie.lean`.
Source: [[decision-problems-v2]] §3.1 Lemma 2 (the converse; T3(b) locates its failure at null
points); repair round 2
Kind: P
Fidelity: exact
Hyps: (a) `0 < ν_C(O_d)` -/
theorem limitOCAt_of_strictOCAt_of_pos [∀ d, Nonempty (acts d)] (s : ι → State Ω K)
    (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (hpos : 0 < nu C B (obs d))
    (hs : StrictOCAt s obs C B d) : LimitOCAt s obs C B d := by
  intro _
  obtain ⟨h1, h2⟩ := hs hpos
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · rw [limitCond_eq_of_pos C B X (obs d) hpos, eq_div_iff hpos.ne']
    exact h1 X
  · rw [limitCond_eq_of_pos C B X (obs d) hpos] at hX
    have hXO : 0 < nu C B (X ∩ obs d) := (div_pos_iff_of_pos_right hpos).mp hX
    have hP : 0 < (s d).pr X :=
      (mul_pos_iff_of_pos_right hpos).mp (by rw [h1 X]; exact hXO)
    obtain ⟨hk, -⟩ := natTrailingDegree_nuPoly_eq_zero C B (X ∩ obs d) hXO
    rw [hk, coeff_zero_nuPoly, coeff_zero_payPoly]
    exact h2 X hP hXO

/-- **At a realized point, limit calibration and strict calibration coincide.**
Source: [[decision-problems-v2]] §3.1 Lemma 2 and its converse; repair round 2
Kind: C
Fidelity: exact
Hyps: (a) `0 < ν_C(O_d)` -/
theorem limitOCAt_iff_strictOCAt_of_pos [∀ d, Nonempty (acts d)] (s : ι → State Ω K)
    (obs : ι → Finset Ω) (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι) (hpos : 0 < nu C B (obs d)) :
    LimitOCAt s obs C B d ↔ StrictOCAt s obs C B d :=
  ⟨limitOCAt_imp_strictOCAt s obs C B d, limitOCAt_of_strictOCAt_of_pos s obs C B d hpos⟩

/-! ## CA-12′'s consequence: ties and the non-forcing of mixed labels -/

section ca12Consequence

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (B : Tree Ω ι acts K)

/-- **The strict act values at `d` are `C(d)`-independent** (CA-12′, in the states): for `C`,
`C'` agreeing off `d`, both realizing `O_d`, with strict states `s`, `s'`, and an act `a` in both
`A_d^+`s, `V_{s_d}(a) = V_{s'_d}(a)`.
Source: `calibration.md` CA-12′ ("the strict act-conditional and act value at `d` do not depend
on `C(d)`"); mandate T15(d)
Kind: C
Fidelity: exact
Hyps: (a) `RecordsForAll`, (a) `C`, `C'` agree off `d`, (a) both positivities, (a) strict OC at
`d` for both -/
theorem V_actEv_eq_of_recordsForAll [∀ d, Nonempty (acts d)] {d : ι}
    (hall : RecordsForAll obs actEv B d) {C C' : Proc ι acts K}
    (hoff : ∀ d', d' ≠ d → C d' = C' d')
    (hpos : 0 < nu C B (obs d)) (hpos' : 0 < nu C' B (obs d))
    {s s' : ι → State Ω K} (hs : StrictOCAt s obs C B d) (hs' : StrictOCAt s' obs C' B d)
    (a : acts d) (ha : a ∈ APlus s actEv d) (ha' : a ∈ APlus s' actEv d) :
    (s d).V (actEv d a) = (s' d).V (actEv d a) := by
  obtain ⟨h1, h2⟩ := hs hpos
  obtain ⟨h1', h2'⟩ := hs' hpos'
  simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
  have hν : 0 < nu C B (actEv d a ∩ obs d) := by
    rw [← h1 (actEv d a)]; exact mul_pos ha hpos
  have hν' : 0 < nu C' B (actEv d a ∩ obs d) := by
    rw [← h1' (actEv d a)]; exact mul_pos ha' hpos'
  have e := h2 (actEv d a) ha hν
  have e' := h2' (actEv d a) ha' hν'
  have cross := ca12_paySum_cross obs actEv B hall hoff a Finset.univ
  rw [Finset.univ_inter] at cross
  have key : (s d).V (actEv d a) * (nu C B (actEv d a ∩ obs d) * nu C' B (actEv d a ∩ obs d)) =
      (s' d).V (actEv d a) * (nu C B (actEv d a ∩ obs d) * nu C' B (actEv d a ∩ obs d)) := by
    calc (s d).V (actEv d a) * (nu C B (actEv d a ∩ obs d) * nu C' B (actEv d a ∩ obs d))
        = paySum C B (actEv d a ∩ obs d) * nu C' B (actEv d a ∩ obs d) := by
          rw [← mul_assoc, e]
      _ = paySum C' B (actEv d a ∩ obs d) * nu C B (actEv d a ∩ obs d) := cross
      _ = (s' d).V (actEv d a) * (nu C B (actEv d a ∩ obs d) * nu C' B (actEv d a ∩ obs d)) := by
          rw [← e']; ring
  exact mul_right_cancel₀ (mul_pos hν hν').ne' key

/-- **A properly mixed calibrated-and-approved label exists only at a tie**: at a recorded
positive point, if `C(d)` supports both `a` and `b` and `T_EDT` approves `C` at `d` with a strict
state `s`, then `V_{s_d}(a) = V_{s_d}(b)`.
Source: `calibration.md` CA-12′ (consequence); [[decision-problems-v2]] Remark 4.3; mandate
T15(d)
Kind: C
Fidelity: exact
Hyps: (a) recording, (a) `0 < ν(O_d)`, (a) strict OC at `d`, (a) `T_EDT` at `d` -/
theorem tie_of_mixed_approved {C : Proc ι acts K} {d : ι}
    (hrec : RecordsFor obs actEv C B d) (hpos : 0 < nu C B (obs d))
    {s : ι → State Ω K} (hs : StrictOCAt s obs C B d) (happ : TEdtAt s actEv C d)
    (a b : acts d) (ha : 0 < (C d).w a) (hb : 0 < (C d).w b) :
    (s d).V (actEv d a) = (s d).V (actEv d b) := by
  have hst : SelfTransparent s actEv C d :=
    selfTransparent_of_recordsFor_strict obs actEv C B s hrec hpos hs
  have hmem : ∀ x, x ∈ APlus s actEv d ↔ 0 < (C d).w x := by
    intro x; simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hst x]
  have hne : (APlus s actEv d).Nonempty := ⟨a, (hmem a).mpr ha⟩
  have hamax := (mem_argmaxPlus s actEv d a).mp (happ hne a ha)
  have hbmax := (mem_argmaxPlus s actEv d b).mp (happ hne b hb)
  exact le_antisymm (hbmax.2 a ((hmem a).mpr ha)) (hamax.2 b ((hmem b).mpr hb))

/-- **A sub-mixture of a strictly calibrated recorded label realizes `O_d`**: under
`RecordsForAll`, if `C'` agrees with `C` off `d`, `supp C'(d) ⊆ supp C(d)`, `C` realizes `O_d`
and is strictly calibrated at `d`, then `ν_{C'}(O_d) > 0`. (Pick `a ∈ supp C'(d)`: the recording
argument gives `ν_C(a ∧ O_d) = C(d)(a)·ν_C(O_d) > 0`, CA-12′'s factorisation makes
`ν(a ∧ O_d) = C(d)(a)·Θ(a)` with `Θ` `C(d)`-free, so `Θ(a) > 0` and `ν_{C'}(a ∧ O_d) > 0`.)
Removes the positivity hypothesis for `C'` from `tEdtAt_of_support_subset_of_recordsForAll`
(audit round 2, adversarial N3 / fidelity N5).
Source: `calibration.md` CA-12′ (consequence); audit round 2
Kind: C
Fidelity: exact
Hyps: (a) `RecordsForAll`, (a) agreement off `d`, (a) support inclusion, (a) `0 < ν_C(O_d)`,
(a) strict OC at `d` for `C` -/
theorem nu_obs_pos_of_support_subset_of_recordsForAll [∀ d, Nonempty (acts d)] {d : ι}
    (hall : RecordsForAll obs actEv B d) {C C' : Proc ι acts K}
    (hoff : ∀ d', d' ≠ d → C d' = C' d')
    (hsupp : ∀ a, 0 < (C' d).w a → 0 < (C d).w a)
    (hpos : 0 < nu C B (obs d)) : 0 < nu C' B (obs d) := by
  obtain ⟨a, ha'⟩ := FinDistr.exists_pos_w' (C' d)
  have ha : 0 < (C d).w a := hsupp a ha'
  -- the recording argument for `C`: `ν_C(a ∧ O_d) = C(d)(a) · ν_C(O_d) > 0`
  have hC : 0 < nu C B (Finset.univ ∩ actEv d a ∩ obs d) := by
    rw [Finset.univ_inter, nu_actEv_inter_obs_of_recordsFor obs actEv C B (hall C) a]
    exact mul_pos ha hpos
  -- CA-12′'s factorisation: `Θ(a) > 0`, and `Θ` is `C(d)`-free
  rw [nu_factor_of_recordsForAll obs actEv B hall C a Finset.univ] at hC
  have hθ : 0 < theta obs B C d a Finset.univ :=
    lt_of_mul_lt_mul_left (by rwa [mul_zero]) ha.le
  have hC' : 0 < nu C' B (Finset.univ ∩ actEv d a ∩ obs d) := by
    rw [nu_factor_of_recordsForAll obs actEv B hall C' a Finset.univ,
      ← theta_congr_off obs B d hoff a Finset.univ]
    exact mul_pos ha' hθ
  exact hC'.trans_le (nu_inter_le C' B _ _)

/-- **Approval transfers to every sub-mixture at `d`** (CA-12′'s "never forced"): under
`RecordsForAll`, if `C'` agrees with `C` off `d` and `supp C'(d) ⊆ supp C(d)`, `C` realizes
`O_d`, `s`, `s'` are strict states for `C`, `C'` at `d`, and `T_EDT` approves `C` at `d` (with
`s`), then `T_EDT` approves `C'` at `d` (with `s'`). (That `C'` realizes `O_d` is derived,
`nu_obs_pos_of_support_subset_of_recordsForAll`; repair round 2 dropped it as a hypothesis.) In
particular each pure label `δ_a`, `a ∈ supp C(d)`, is calibrated-and-approved alongside the
mixed one: calibration plus approval never pins a mixed label.
Source: `calibration.md` CA-12′ (consequence: "never forced"); mandate T15(d)
Kind: C
Fidelity: exact
Hyps: (a) `RecordsForAll`, (a) agreement off `d`, (a) support inclusion, (a) `0 < ν_C(O_d)`,
(a) strict OC at `d` for both, (a) `T_EDT` at `d` for `C` -/
theorem tEdtAt_of_support_subset_of_recordsForAll [∀ d, Nonempty (acts d)] {d : ι}
    (hall : RecordsForAll obs actEv B d) {C C' : Proc ι acts K}
    (hoff : ∀ d', d' ≠ d → C d' = C' d')
    (hsupp : ∀ a, 0 < (C' d).w a → 0 < (C d).w a)
    (hpos : 0 < nu C B (obs d))
    {s s' : ι → State Ω K} (hs : StrictOCAt s obs C B d) (hs' : StrictOCAt s' obs C' B d)
    (happ : TEdtAt s actEv C d) : TEdtAt s' actEv C' d := by
  have hpos' : 0 < nu C' B (obs d) :=
    nu_obs_pos_of_support_subset_of_recordsForAll obs actEv B hall hoff hsupp hpos
  have hst : SelfTransparent s actEv C d :=
    selfTransparent_of_recordsFor_strict obs actEv C B s (hall C) hpos hs
  have hst' : SelfTransparent s' actEv C' d :=
    selfTransparent_of_recordsFor_strict obs actEv C' B s' (hall C') hpos' hs'
  have hmem : ∀ x, x ∈ APlus s actEv d ↔ 0 < (C d).w x := by
    intro x; simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hst x]
  have hmem' : ∀ x, x ∈ APlus s' actEv d ↔ 0 < (C' d).w x := by
    intro x; simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hst' x]
  intro _ a ha'
  have ha : 0 < (C d).w a := hsupp a ha'
  have hne : (APlus s actEv d).Nonempty := ⟨a, (hmem a).mpr ha⟩
  have hamax := (mem_argmaxPlus s actEv d a).mp (happ hne a ha)
  rw [mem_argmaxPlus]
  refine ⟨(hmem' a).mpr ha', fun b hb => ?_⟩
  have hbC : b ∈ APlus s actEv d := (hmem b).mpr (hsupp b ((hmem' b).mp hb))
  have hle := hamax.2 b hbC
  rw [← V_actEv_eq_of_recordsForAll obs actEv B hall hoff hpos hpos' hs hs' a
      ((hmem a).mpr ha) ((hmem' a).mpr ha'),
    ← V_actEv_eq_of_recordsForAll obs actEv B hall hoff hpos hpos' hs hs' b hbC hb]
  exact hle

end ca12Consequence

end Cleanroom.Decision.DpCalibration
