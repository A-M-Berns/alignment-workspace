import Cleanroom.Decision.DpReferentsCdt.Poly
import Cleanroom.Decision.DpCalibration.Corollaries

/-!
# Theorem C2-A′, the recording theorem FA-20′, and Theorem C2-B′ (surviving form)

**Theorem C2-A′** (`C2.md` line 50; T3): under Definition 6 at an F3′-structural point with
Definition 3's disjointness, `ν_C(O_d) > 0` and strict observation calibration, (i) the strict
evidential act value equals `refR2Real` on `A_d^+` (`evStrict_eq_refR2Real_of_APlus`), (ii)
`refR3 = refR2Real` on all of `A_d` (Lemma C2-L3, `Poly.lean`), hence (`evExt_eq_refR2Real`) the
R3-extended evidential value **is** the tree-intrinsic `refR2Real` — with no `cf` in sight — and
(iii) for a `cf` slot counterfactually calibrated to `refR2Real` or to `refR3`, `T_EDT`(R3-extended)
and `T_CDT` approve the same labels (`tEdtExtAt_iff_tCdtAt_of_calibrated`,
`tEdtExtAt_iff_tCdtAt_of_calibrated_refR3`); the (b-int) reading for full-support labels
(`tEdtAt_iff_tCdtAt_of_fullSupport`) and the vacuous approval of pure labels
(`tEdtAt_of_deterministic_actRecording`).

**The recording theorem FA-20′** (T5): (i) `refR2Real = refR3` under F3′ for the trembles
(`refR2Real_eq_refR3_of_trembles`); (ii) `refR1State = refR3` under recording for the trembles
(`refR1State_eq_refR3_of_trembles`); (iii) all three equal the strict conditional on positive acts
(`refR3_eq_condExp_of_pos`, `evStrict_eq_refR3_of_APlus`); (iv) dp-sl-2-061(i) under Definition 7
recording for `C` alone (`referents_agree_of_recordsFor`, with the F3′ clause needed for `refR2Real`
stated separately); (v) FA-25′(2′): totality of `refR3` and its agreement with the limit state
(`nuPoly_actEv_inter_obs_ne_zero_of_recordsForAll`, `evStrict_eq_refR3_of_limitOC`).

**Theorem C2-B′, surviving form** (T6): under C2-A′'s hypotheses and recording for every
procedure, `refR1State = refR2Real` (`refR1State_eq_refR2Real_of_recordsForAll`), `refR2Real` at
every label is the label-free `refR1State` (`refR2Real_deviate_eq_refR1State`), the approved set
is the fixed face (`tEdtExtAt_deviate_iff_fixedFace`) and no properly mixed label is forced
(`pure_approved_of_approved`, `tie_of_approved_mixed`). The `RecordsForDeviations` form (Open 11)
is proved here at full-support labels (`refR1State_eq_refR2Real_deviate_of_fullSupport`); the
label in play is closed in `C2B.lean` (`c2B_of_recordsForDeviations`, continuation 1 — the first
pass had it as the OPEN stub `c2B_of_recordsForDeviations_open`, now removed).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpReferentsCdt

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ## Theorem C2-A′ -/

section c2a

variable (s : ι → State Ω K) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **C2-A′ (i): the strict evidential act value is `refR2Real` on `A_d^+`** at an F3′ point with
disjointness, `ν_C(O_d) > 0` and strict calibration: `V_{s_d}(a) = refR2Real a` — an identity between
the state's value and the tree-intrinsic forcing referent, with no `cf` in the statement.
Source: `C2.md` line 50 (Theorem C2-A′, "`V_{s_d}(a) = v_d(a; C)` wherever defined"); dp-sl-025;
mandate T3 (i)
Kind: C
Fidelity: exact
Hyps: (a) `ActRecording obs actEv C B d` (F3′ for `C`), (a) `ActEvDisjoint actEv d`,
(a) `0 < ν_C(O_d)`, (a) `StrictOCAt s obs C B d` -/
theorem evStrict_eq_refR2Real_of_APlus {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d)
    {a : acts d} (ha : a ∈ APlus s actEv d) :
    evStrict s actEv d a = refR2Real actEv C B d a := by
  have haC : 0 < (C d).w a :=
    (mem_APlus_iff_of_actRecording_strict obs actEv C B s h hdisj hpos hs a).mp ha
  have hν := nu_actEv_inter_obs_pos obs actEv C B h hdisj haC hpos
  have hP : 0 < (s d).pr (actEv d a) := by
    simpa [APlus] using ha
  have h2 := (hs hpos).2 (actEv d a) hP hν
  rw [← condExp_actEv_inter_obs_eq_refR2Real obs actEv C B h hdisj haC hpos]
  unfold evStrict condExp
  rw [← h2]
  field_simp

/-- **C2-A′ (i)+(ii): the R3-extended evidential value is `refR2Real` on all of `A_d`** at an
F3′-structural point — the strong tickle defence: strictly calibrated evidential conditioning, its
tremble limit and single-instance forcing at the real node are one function of the label, because the
label factor cancels, whatever simulations of `d` sit upstream. No `cf` appears.
Source: `C2.md` line 50 (Theorem C2-A′: "the R3 extension of `V_{s_d}` equals `V^a_{s_d}(a) = v_d(a; C)`
everywhere"); `sl-synthesis.md` §2.2; dp-sl-025; mandate T3
Kind: C
Fidelity: exact
Hyps: (a) `ActRecordingStructural obs actEv B d`, (a) `ActEvDisjoint actEv d`, (a) `0 < ν_C(O_d)`,
(a) `StrictOCAt s obs C B d` -/
theorem evExt_eq_refR2Real {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d)
    (a : acts d) : evExt s obs actEv C B d a = refR2Real actEv C B d a := by
  unfold evExt
  split_ifs with ha
  · exact evStrict_eq_refR2Real_of_APlus s obs actEv C B (hS.actRecording C) hdisj hpos hs ha
  · exact refR3_eq_refR2Real_of_structural obs actEv C B hS hdisj hpos a

/-- **C2-A′ (iii), `refR2Real`-calibrated `cf`**: at an F3′-structural point with strict calibration,
for a `cf` slot counterfactually calibrated to `refR2Real` on all of `A_d`,
`T_EDT`(R3-extended) approves `C` at `d` iff `T_CDT` does. Stated for the procedure `C`; the
label-quantified form is its instance at `C[d ↦ m]` with the strict state of the label.
Source: `C2.md` line 50 (Theorem C2-A′: "the calibrated-and-approved mixed labels … coincide for
`T_EDT`(R3-extended) and `T_CDT` with either referent"); mandate T3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) as `evExt_eq_refR2Real`, (a) `CfCalibratedAt cf d (refR2Real …) ⊤` (hypothesis (c) of
C2-A′: counterfactual calibration, used in this clause only) -/
theorem tEdtExtAt_iff_tCdtAt_of_calibrated {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d)
    (cf : Cf ι acts K) (hcf : CfCalibratedAt cf d (refR2Real actEv C B d) (fun _ => True)) :
    TEdtExtAt s obs actEv C B d ↔ TCdtAt cf C d := by
  unfold TEdtExtAt TCdtAt
  simp only [evExt_eq_refR2Real s obs actEv C B hS hdisj hpos hs, hcf _ trivial]

/-- **C2-A′ (iii), `refR3`-calibrated `cf`**: the same coincidence for a `cf` slot calibrated to
`refR3` on all of `A_d`.
Source: `C2.md` line 50 (Theorem C2-A′, "with either referent"); mandate T3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) as above, (a) `CfCalibratedAt cf d (refR3 …) ⊤` -/
theorem tEdtExtAt_iff_tCdtAt_of_calibrated_refR3 {d : ι}
    (hS : ActRecordingStructural obs actEv B d) (hdisj : ActEvDisjoint actEv d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) (cf : Cf ι acts K)
    (hcf : CfCalibratedAt cf d (refR3 obs actEv C B d) (fun _ => True)) :
    TEdtExtAt s obs actEv C B d ↔ TCdtAt cf C d := by
  apply tEdtExtAt_iff_tCdtAt_of_calibrated s obs actEv C B hS hdisj hpos hs cf
  intro a _
  rw [hcf a trivial, refR3_eq_refR2Real_of_structural obs actEv C B hS hdisj hpos a]

/-- **C2-A′, the (b-int) reading**: for a full-support label, `dp-calibration`'s `T_EDT` (domain
`A_d^+`, here all of `A_d` by self-transparency) and `T_CDT` with a `refR2Real`-calibrated `cf`
coincide.
Source: `C2.md` line 50 (Theorem C2-A′, "With (b-int) … coincidence on full-support labels");
mandate T3 (iii)
Kind: C
Fidelity: exact
Hyps: (a) as above, (a) `∀ a, 0 < C(d)(a)`, (a) `CfCalibratedAt cf d (refR2Real …) ⊤` -/
theorem tEdtAt_iff_tCdtAt_of_fullSupport {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d)
    (hfull : ∀ a, 0 < (C d).w a) (cf : Cf ι acts K)
    (hcf : CfCalibratedAt cf d (refR2Real actEv C B d) (fun _ => True)) :
    TEdtAt s actEv C d ↔ TCdtAt cf C d := by
  have hmem : ∀ a, a ∈ APlus s actEv d :=
    fun a => (mem_APlus_iff_of_actRecording_strict obs actEv C B s h hdisj hpos hs a).mpr (hfull a)
  have hV : ∀ a, (s d).V (actEv d a) = cf d a := fun a => by
    rw [hcf a trivial]
    exact evStrict_eq_refR2Real_of_APlus s obs actEv C B h hdisj hpos hs (hmem a)
  unfold TEdtAt TCdtAt
  constructor
  · intro hE a ha b
    have := (mem_argmaxPlus s actEv d a).mp (hE ⟨a, hmem a⟩ a ha)
    rw [← hV a, ← hV b]
    exact this.2 b (hmem b)
  · intro hC _ a ha
    rw [mem_argmaxPlus]
    refine ⟨hmem a, fun b _ => ?_⟩
    rw [hV a, hV b]
    exact hC a ha b

/-- **Pure labels are `T_EDT`-approved vacuously at an F3′ point** (Remark 3.9's collapse, here
under F3′ rather than Definition 7): `A_d^+ = {C(d)}` and the `T_EDT` clause holds.
Source: [[decision-problems-v2]] Remark 3.9; `C2.md` line 50 ("`T_EDT` additionally approves every
pure label vacuously"); mandate §7 trap 6
Kind: C
Fidelity: exact (per point, with the positivity)
Hyps: (a) `ActRecording`, (a) disjointness, (a) `0 < ν_C(O_d)`, (a) strict OC, (a) `C d = δ_{a₀}` -/
theorem tEdtAt_of_deterministic_actRecording {d : ι} (h : ActRecording obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d)
    (a₀ : acts d) (hC : C d = FinDistr.pure a₀) :
    APlus s actEv d = {a₀} ∧ TEdtAt s actEv C d := by
  have hmem : ∀ a, a ∈ APlus s actEv d ↔ a = a₀ := by
    intro a
    rw [mem_APlus_iff_of_actRecording_strict obs actEv C B s h hdisj hpos hs a, hC,
      FinDistr.pure_w]
    constructor
    · intro hlt; by_contra hne; rw [if_neg hne] at hlt; exact lt_irrefl 0 hlt
    · rintro rfl; simp
  refine ⟨?_, fun _ a ha => ?_⟩
  · ext a; rw [hmem a, Finset.mem_singleton]
  · have haa : a = a₀ := by
      rw [hC, FinDistr.pure_w] at ha
      by_contra hne; rw [if_neg hne] at ha; exact lt_irrefl 0 ha
    subst haa
    rw [mem_argmaxPlus]
    refine ⟨(hmem a).mpr rfl, fun b hb => ?_⟩
    rw [(hmem b).mp hb]

end c2a

/-! ## The recording theorem FA-20′ -/

section recordingThm

variable (s : ι → State Ω K) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **FA-20′(i): `refR2Real = refR3` under F3′ for the trembles** (with disjointness and
`ν_C(O_d) > 0`), on every act.
Source: `faithful.md` FA-20′(i); dp-cf-109; mandate T5(i)
Kind: C
Fidelity: exact
Hyps: (a) `ActRecordingTrembles obs actEv C B d`, (a) disjointness, (a) `0 < ν_C(O_d)` -/
theorem refR2Real_eq_refR3_of_trembles {d : ι} (hT : ActRecordingTrembles obs actEv C B d)
    (hdisj : ActEvDisjoint actEv d) (hpos : 0 < nu C B (obs d)) (a : acts d) :
    refR2Real actEv C B d a = refR3 obs actEv C B d a :=
  (refR3_eq_refR2Real_of_structural obs actEv C B
    ((actRecordingStructural_iff_trembles C B d).mpr hT) hdisj hpos a).symm

/-- **FA-20′(ii): `refR1State = refR3` under Definition 7 recording for the trembles**, wherever
the deviation realizes `O_d`.
Source: `faithful.md` FA-20′(ii); dp-cf-109; mandate T5(ii)
Kind: C
Fidelity: exact
Hyps: (a) `RecordsForTrembles obs actEv C B d`, (a) `0 < ν_{C[d↦a]}(O_d)` -/
theorem refR1State_eq_refR3_of_trembles {d : ι} (hT : RecordsForTrembles obs actEv C B d)
    (a : acts d) (hpos : 0 < nu (C.deviatePure d a) B (obs d)) :
    refR1State obs C B d a = refR3 obs actEv C B d a :=
  (refR3_eq_refR1State_of_recordsForAll obs actEv C B
    ((recordsForTrembles_iff_recordsForAll C B d).mp hT) a hpos).symm

/-- **FA-20′(iii), first half: at a positive act the tremble limit is the strict conditional**
(no recording needed).
Source: `faithful.md` FA-20′(iii) ("Lemma 2's mechanism"); mandate T5(iii)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ν_C(a ∧ O_d)` -/
theorem refR3_eq_condExp_of_pos {d : ι} {a : acts d} (hpos : 0 < nu C B (actEv d a ∩ obs d)) :
    refR3 obs actEv C B d a = condExp C B (actEv d a ∩ obs d) := by
  unfold refR3 limitVal condExp
  rw [(natTrailingDegree_nuPoly_eq_zero C B _ hpos).1, coeff_zero_nuPoly, coeff_zero_payPoly]

/-- **FA-20′(iii), second half: at a subjectively possible act the strict value is `refR3`**
(strict calibration at a realized point).
Source: `faithful.md` FA-20′(iii) ("all three agree with Jeffrey conditioning at the strictly …
calibrated state on positive acts"); mandate T5(iii)
Kind: C
Fidelity: exact
Hyps: (a) `StrictOCAt`, (a) `0 < ν_C(O_d)`, (a) `a ∈ A_d^+`, (a) `0 < ν_C(a ∧ O_d)` -/
theorem evStrict_eq_refR3_of_APlus {d : ι} (hs : StrictOCAt s obs C B d)
    (hpos : 0 < nu C B (obs d)) {a : acts d} (ha : a ∈ APlus s actEv d)
    (hν : 0 < nu C B (actEv d a ∩ obs d)) :
    evStrict s actEv d a = refR3 obs actEv C B d a := by
  have hP : 0 < (s d).pr (actEv d a) := by simpa [APlus] using ha
  have h2 := (hs hpos).2 (actEv d a) hP hν
  rw [refR3_eq_condExp_of_pos obs actEv C B hν]
  unfold evStrict condExp
  rw [← h2]
  field_simp

/-- **dp-sl-2-061(i): at a Definition-7-recorded, strictly calibrated point the strict value,
R1-state and R3 coincide on `A_d^+`** (recording for the given `C` only; for `C(d)(a) > 0` the
`C[d↦a]`-positive `O_d`-runs are among `C`'s, so recording is inherited). The `refR2Real` clause of
the survey's statement needs F3′ for `C` and disjointness in addition (`referents_agree_of_recordsFor_actRecording`;
findings F3).
Source: dp-sl-2-061(i); `faithful.md` FA-20′ takeaway; mandate T5(iv)
Kind: C
Fidelity: weaker: the `refR2Real` clause is separated out (it needs F3′ for `C`)
Hyps: (a) `RecordsFor obs actEv C B d`, (a) `0 < ν_C(O_d)`, (a) `StrictOCAt`, (a) `a ∈ A_d^+` -/
theorem referents_agree_of_recordsFor {d : ι} (h : RecordsFor obs actEv C B d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) {a : acts d}
    (ha : a ∈ APlus s actEv d) :
    evStrict s actEv d a = refR1State obs C B d a ∧
      evStrict s actEv d a = refR3 obs actEv C B d a := by
  have hst := selfTransparent_of_recordsFor_strict obs actEv C B s h hpos hs
  have haC : 0 < (C d).w a := by
    have := (by simpa [APlus] using ha : 0 < (s d).pr (actEv d a))
    rwa [hst a] at this
  have hν : 0 < nu C B (actEv d a ∩ obs d) := by
    rw [nu_actEv_inter_obs_of_recordsFor obs actEv C B h a]; exact mul_pos haC hpos
  refine ⟨?_, evStrict_eq_refR3_of_APlus s obs actEv C B hs hpos ha hν⟩
  rw [refR1State_eq_condExp_of_recordsFor obs actEv C B h haC hν,
    ← refR3_eq_condExp_of_pos obs actEv C B hν]
  exact evStrict_eq_refR3_of_APlus s obs actEv C B hs hpos ha hν

/-- **dp-sl-2-061(i) with the forcing referent**: adding F3′ for `C` and disjointness, all four —
`evStrict`, `refR1State`, `refR2Real`, `refR3` — coincide on `A_d^+`.
Source: dp-sl-2-061(i); mandate T5(iv)
Kind: C
Fidelity: exact
Hyps: (a) `RecordsFor`, (a) `ActRecording`, (a) disjointness, (a) `0 < ν_C(O_d)`, (a) strict OC,
(a) `a ∈ A_d^+` -/
theorem referents_agree_of_recordsFor_actRecording {d : ι} (h : RecordsFor obs actEv C B d)
    (hA : ActRecording obs actEv C B d) (hdisj : ActEvDisjoint actEv d)
    (hpos : 0 < nu C B (obs d)) (hs : StrictOCAt s obs C B d) {a : acts d}
    (ha : a ∈ APlus s actEv d) :
    evStrict s actEv d a = refR1State obs C B d a ∧
      evStrict s actEv d a = refR2Real actEv C B d a ∧
      evStrict s actEv d a = refR3 obs actEv C B d a :=
  ⟨(referents_agree_of_recordsFor s obs actEv C B h hpos hs ha).1,
    evStrict_eq_refR2Real_of_APlus s obs actEv C B hA hdisj hpos hs ha,
    (referents_agree_of_recordsFor s obs actEv C B h hpos hs ha).2⟩

/-- Every subtree has a chance-positive leaf. Source: none: infrastructure. Kind: L -/
theorem exists_chancePos_leaf :
    (T : Tree Ω ι acts K) → ∃ ℓ : T.Leaves, 0 < chanceWeight T ℓ
  | .leaf _ _ => ⟨(), one_pos⟩
  | .chance _ β child => by
      obtain ⟨i, hi⟩ := FinDistr.exists_pos_w' β
      obtain ⟨ℓ, hℓ⟩ := exists_chancePos_leaf (child i)
      exact ⟨⟨i, ℓ⟩, by simp only [chanceWeight_chance]; exact mul_pos hi hℓ⟩
  | .decision d child => by
      obtain ⟨ℓ, hℓ⟩ := exists_chancePos_leaf (child (Classical.arbitrary (acts d)))
      exact ⟨⟨_, ℓ⟩, by simpa [chanceWeight_decision] using hℓ⟩

/-- If a chance-positive leaf passes `q`, then for every act `a` some chance-positive leaf takes the
`a`-edge at `q`.
Source: none: infrastructure (`faithful.md` FA-17′(b): "each edge does")
Kind: L -/
theorem exists_chancePos_edge :
    (B : Tree Ω ι acts K) → ∀ (q : B.DecNode) (ℓ : B.Leaves), 0 < chanceWeight B ℓ →
      (edgeOf B q ℓ).isSome → ∀ a : acts (pt B q),
      ∃ ℓ' : B.Leaves, 0 < chanceWeight B ℓ' ∧ edgeOf B q ℓ' = some a
  | .leaf _ _, q, _, _, _, _ => q.elim
  | .chance _ β child, ⟨i, q⟩, ⟨j, ℓ⟩, hpos, he, a => by
      simp only [edgeOf_chance] at he
      by_cases hij : j = i
      · subst hij
        simp only [dite_true] at he
        simp only [chanceWeight_chance] at hpos
        have hi : 0 < β.w j := by
          rcases (β.nonneg j).lt_or_eq with h | h
          · exact h
          · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
        have hrest : 0 < chanceWeight (child j) ℓ := by
          rcases (chanceWeight_nonneg (child j) ℓ).lt_or_eq with h | h
          · exact h
          · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
        obtain ⟨ℓ', h1, h2⟩ := exists_chancePos_edge (child j) q ℓ hrest he a
        exact ⟨⟨j, ℓ'⟩, by simp only [chanceWeight_chance]; exact mul_pos hi h1,
          by simp [edgeOf_chance, h2]⟩
      · simp [hij] at he
  | .decision d child, none, ⟨b, ℓ⟩, _, _, a => by
      obtain ⟨ℓ', hℓ'⟩ := exists_chancePos_leaf (child a)
      exact ⟨⟨a, ℓ'⟩, by simpa [chanceWeight_decision] using hℓ', by simp [edgeOf_decision_none]⟩
  | .decision d child, some ⟨c, q⟩, ⟨b, ℓ⟩, hpos, he, a => by
      simp only [edgeOf_decision_some] at he
      by_cases hbc : b = c
      · subst hbc
        simp only [dite_true] at he
        simp only [chanceWeight_decision] at hpos
        obtain ⟨ℓ', h1, h2⟩ := exists_chancePos_edge (child b) q ℓ hpos he a
        exact ⟨⟨b, ℓ'⟩, by simpa [chanceWeight_decision] using h1,
          by simp [edgeOf_decision_some, h2]⟩
      · simp [hbc] at he

/-- **FA-25′(2′), totality: under recording for every procedure with `O_d` tremble-realizable,
every act is tremble-reachable within `O_d`** (`nuPoly (a ∧ O_d) ≠ 0` for every `a`), so `refR3` is
total on `A_d`.
Source: `faithful.md` FA-17′(b), FA-25′(2′) ("R3 is total on `A_d`"); mandate T5(v)
Kind: P
Fidelity: exact
Hyps: (a) `RecordsForAll obs actEv B d`, (a) `nuPoly C B (obs d) ≠ 0` -/
theorem nuPoly_actEv_inter_obs_ne_zero_of_recordsForAll {d : ι}
    (hall : RecordsForAll obs actEv B d) (hO : nuPoly C B (obs d) ≠ 0) (a : acts d) :
    nuPoly C B (actEv d a ∩ obs d) ≠ 0 := by
  obtain ⟨ℓ, hobs, hpos⟩ := (nuPoly_ne_zero_iff C B (obs d)).mp hO
  have hU : 0 < leafLaw (uniformProc (K := K)) B ℓ := leafLaw_uniformProc_pos B ℓ hpos
  obtain ⟨h1, hnode⟩ := hall uniformProc ℓ hU hobs
  have hcard := h1
  rw [count_eq_card_dNodesOn, Finset.card_eq_one] at hcard
  obtain ⟨q, hq⟩ := hcard
  have hmem : q ∈ dNodesOn B d ℓ := by rw [hq]; exact Finset.mem_singleton_self q
  rw [mem_dNodesOn] at hmem
  obtain ⟨hpt, hsome⟩ := hmem
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hsv, -, -⟩ := hnode q hpt b hb
  subst hpt
  obtain ⟨ℓ', hpos', he'⟩ := exists_chancePos_edge B q ℓ hpos hsome a
  rw [nuPoly_ne_zero_iff]
  refine ⟨ℓ', ?_, hpos'⟩
  have hU' : 0 < leafLaw (uniformProc (K := K)) B ℓ' := leafLaw_uniformProc_pos B ℓ' hpos'
  have hobs' : world B ℓ' ∈ obs (pt B q) :=
    hsv ℓ' ((mem_leavesBelow B q ℓ').mpr (by rw [he']; rfl))
  obtain ⟨-, hact', -⟩ := (hall uniformProc ℓ' hU' hobs').2 q rfl a he'
  exact Finset.mem_inter.mpr ⟨hact', hobs'⟩

/-- **FA-25′(2′), the limit state's values are `refR3`**: under limit calibration at `d` with `O_d`
tremble-realizable, at every act of positive limiting probability the state's value is `refR3`.
Source: `faithful.md` FA-25′(2′); [[decision-problems-v2]] Definition 10; mandate T5(v)
Kind: C
Fidelity: exact (the limit taken algebraically)
Hyps: (a) `LimitOCAt s obs C B d`, (a) `nuPoly C B (obs d) ≠ 0`, (a) `0 < limitCond C B (a) (O_d)` -/
theorem evStrict_eq_refR3_of_limitOC {d : ι} (hl : LimitOCAt s obs C B d)
    (hO : nuPoly C B (obs d) ≠ 0) {a : acts d} (ha : 0 < limitCond C B (actEv d a) (obs d)) :
    evStrict s actEv d a = refR3 obs actEv C B d a := by
  obtain ⟨-, h2⟩ := hl hO
  have e := h2 (actEv d a) ha
  have hne : nuPoly C B (actEv d a ∩ obs d) ≠ 0 := by
    intro hz
    unfold limitCond at ha
    rw [hz, Polynomial.coeff_zero, zero_div] at ha
    exact lt_irrefl 0 ha
  have hc : 0 < (nuPoly C B (actEv d a ∩ obs d)).coeff
      (nuPoly C B (actEv d a ∩ obs d)).natTrailingDegree :=
    trailingCoeff_nuPoly_pos C B _ hne
  unfold evStrict refR3 limitVal
  rw [← e]
  field_simp

end recordingThm

/-! ## Theorem C2-B′, surviving form -/

section c2b

variable (s : ι → State Ω K) (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  (C : Proc ι acts K) (B : Tree Ω ι acts K)

/-- **C2-B′ (`RecordsForAll` form): `refR1State = refR2Real`** under C2-A′'s hypotheses and
Definition 7 recording for every procedure, wherever the deviation realizes `O_d`.
Source: `C2.md` line 54 (Theorem C2-B′, WOUNDED form: "records at `d` in Definition 7's sense for
every `C[d ↦ m]`"), proved here under the stronger `RecordsForAll` (Open 11); dp-sl-026; mandate T6
Kind: C
Fidelity: weaker: `RecordsForAll` in place of `RecordsForDeviations` (Open 11)
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsForAll`, (a) `0 < ν_C(O_d)`,
(a) `0 < ν_{C[d↦a]}(O_d)` -/
theorem refR1State_eq_refR2Real_of_recordsForAll {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hall : RecordsForAll obs actEv B d)
    (hpos : 0 < nu C B (obs d)) (a : acts d) (hpa : 0 < nu (C.deviatePure d a) B (obs d)) :
    refR1State obs C B d a = refR2Real actEv C B d a := by
  rw [← refR3_eq_refR1State_of_recordsForAll obs actEv C B hall a hpa,
    refR3_eq_refR2Real_of_structural obs actEv C B hS hdisj hpos a]

/-- **C2-B′, label-freedom: `refR2Real` at every label `m` is the label-free `refR1State` of `C`**
(the deviation at `d` of `C[d ↦ m]` is the deviation of `C`).
Source: `C2.md` line 54 (Theorem C2-B′: "the common value `v_d(a)` does not depend on `C(d)`");
mandate T6
Kind: C
Fidelity: weaker: under `RecordsForAll`
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsForAll`, (a) `0 < ν_{C[d↦m]}(O_d)`,
(a) `0 < ν_{C[d↦a]}(O_d)` -/
theorem refR2Real_deviate_eq_refR1State {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hall : RecordsForAll obs actEv B d)
    (m : FinDistr K (acts d)) (hpm : 0 < nu (C.deviate d m) B (obs d)) (a : acts d)
    (hpa : 0 < nu (C.deviatePure d a) B (obs d)) :
    refR2Real actEv (C.deviate d m) B d a = refR1State obs C B d a := by
  rw [← refR1State_eq_refR2Real_of_recordsForAll obs actEv (C.deviate d m) B hS hdisj hall hpm a
    (by unfold Proc.deviatePure; rw [deviate_deviate']; exact hpa)]
  unfold refR1State Proc.deviatePure
  rw [deviate_deviate']

/-- **C2-B′, the fixed face**: under C2-A′'s hypotheses at the label `m` and recording for every
procedure, `T_EDT`(R3-extended) approves `C[d ↦ m]` iff `supp m ⊆ argmax_a v_d(a)` with the
label-free `v_d := refR1State obs C B d`.
Source: `C2.md` line 54 (Theorem C2-B′: "the calibrated-and-approved set is the fixed face
`{m : supp m ⊆ argmax_a v_d(a)}`"); mandate T6
Kind: C
Fidelity: weaker: under `RecordsForAll`
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsForAll`, (a) `0 < ν_{C[d↦m]}(O_d)`,
(a) `StrictOCAt` for `C[d↦m]`, (a) `∀ a, 0 < ν_{C[d↦a]}(O_d)` -/
theorem tEdtExtAt_deviate_iff_fixedFace {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hall : RecordsForAll obs actEv B d)
    (m : FinDistr K (acts d)) (hpm : 0 < nu (C.deviate d m) B (obs d))
    (hs : StrictOCAt s obs (C.deviate d m) B d)
    (hpa : ∀ a, 0 < nu (C.deviatePure d a) B (obs d)) :
    TEdtExtAt s obs actEv (C.deviate d m) B d ↔
      ∀ a, 0 < m.w a → ∀ b, refR1State obs C B d b ≤ refR1State obs C B d a := by
  unfold TEdtExtAt
  simp only [evExt_eq_refR2Real s obs actEv (C.deviate d m) B hS hdisj hpm hs,
    refR2Real_deviate_eq_refR1State obs actEv C B hS hdisj hall m hpm _ (hpa _),
    Proc.deviate_same]

/-- **No properly mixed label is forced**: if `T_EDT`(R3-extended) approves a label `m` with
`a, b ∈ supp m`, then `v_d(a) = v_d(b)` — a mixed approved label exists only at a tie.
Source: `C2.md` line 54 (Theorem C2-B′: "no mixed label is forced (CA-12′(iii))"); mandate T6
Kind: C
Fidelity: weaker: under `RecordsForAll`
Hyps: (a) as `tEdtExtAt_deviate_iff_fixedFace` -/
theorem tie_of_approved_mixed {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hall : RecordsForAll obs actEv B d)
    (m : FinDistr K (acts d)) (hpm : 0 < nu (C.deviate d m) B (obs d))
    (hs : StrictOCAt s obs (C.deviate d m) B d)
    (hpa : ∀ a, 0 < nu (C.deviatePure d a) B (obs d))
    (happ : TEdtExtAt s obs actEv (C.deviate d m) B d) {a b : acts d} (ha : 0 < m.w a)
    (hb : 0 < m.w b) : refR1State obs C B d a = refR1State obs C B d b := by
  rw [tEdtExtAt_deviate_iff_fixedFace s obs actEv C B hS hdisj hall m hpm hs hpa] at happ
  exact le_antisymm (happ b hb a) (happ a ha b)

/-- **Every pure label in the support of an approved label is approved** (with its own strict
state): calibration plus approval never pins a mixed label.
Source: `C2.md` line 54 (Theorem C2-B′); `dp-calibration`'s `tEdtAt_of_support_subset_of_recordsForAll`;
mandate T6
Kind: C
Fidelity: weaker: under `RecordsForAll`
Hyps: (a) as `tEdtExtAt_deviate_iff_fixedFace`, for both labels -/
theorem pure_approved_of_approved {d : ι} (hS : ActRecordingStructural obs actEv B d)
    (hdisj : ActEvDisjoint actEv d) (hall : RecordsForAll obs actEv B d)
    (m : FinDistr K (acts d)) (hpm : 0 < nu (C.deviate d m) B (obs d))
    (hs : StrictOCAt s obs (C.deviate d m) B d)
    (hpa : ∀ a, 0 < nu (C.deviatePure d a) B (obs d))
    (happ : TEdtExtAt s obs actEv (C.deviate d m) B d) {a : acts d} (ha : 0 < m.w a)
    (s' : ι → State Ω K) (hs' : StrictOCAt s' obs (C.deviatePure d a) B d) :
    TEdtExtAt s' obs actEv (C.deviatePure d a) B d := by
  rw [tEdtExtAt_deviate_iff_fixedFace s obs actEv C B hS hdisj hall m hpm hs hpa] at happ
  rw [Proc.deviatePure, tEdtExtAt_deviate_iff_fixedFace s' obs actEv C B hS hdisj hall _ (hpa a)
    hs' hpa]
  intro a' ha' b
  have : a' = a := by
    rw [FinDistr.pure_w] at ha'
    by_contra hne; rw [if_neg hne] at ha'; exact lt_irrefl 0 ha'
  subst this
  exact happ a' ha b

/-- **C2-B′ at full-support labels under `RecordsForDeviations`**: `refR1State` of `C` is `refR2Real`
at every full-support label `m` — recording for the deviations of `C` suffices here, since `C[d↦m]`
is itself a deviation and `C[d↦m][d↦a] = C[d↦a]`.
Source: `C2.md` line 54 (Theorem C2-B′, WOUNDED form); `repair/C1.md` Open 11; mandate T6
Kind: C
Fidelity: exact for full-support labels (the label `C(d)` itself is Open 11)
Hyps: (a) `ActRecordingStructural`, (a) disjointness, (a) `RecordsForDeviations obs actEv C B d`,
(a) `∀ a, 0 < m(a)` -/
theorem refR1State_eq_refR2Real_deviate_of_fullSupport {d : ι}
    (hS : ActRecordingStructural obs actEv B d) (hdisj : ActEvDisjoint actEv d)
    (hdev : RecordsForDeviations obs actEv C B d) (m : FinDistr K (acts d))
    (hm : ∀ a, 0 < m.w a) (a : acts d) :
    refR1State obs C B d a = refR2Real actEv (C.deviate d m) B d a := by
  have hrec : RecordsFor obs actEv (C.deviate d m) B d := hdev m
  have hA : ActRecording obs actEv (C.deviate d m) B d := hS.actRecording _
  have hma : 0 < ((C.deviate d m) d).w a := by rw [Proc.deviate_same]; exact hm a
  have hν := nu_deviatePure_obs_mul obs actEv (C.deviate d m) B hrec hma
  have hp := paySum_deviatePure_obs_mul obs actEv (C.deviate d m) B hrec hma
  rw [nu_actEv_inter_obs_eq obs actEv _ B hA hdisj a] at hν
  rw [paySum_actEv_inter_obs_eq obs actEv _ B hA hdisj a] at hp
  unfold Proc.deviatePure at hν hp
  rw [deviate_deviate'] at hν hp
  have hν' : nu (C.deviate d (FinDistr.pure a)) B (obs d) = realReach actEv (C.deviate d m) B d :=
    mul_right_cancel₀ hma.ne' (by rw [hν]; ring)
  have hp' : paySum (C.deviate d (FinDistr.pure a)) B (obs d) =
      realForced actEv (C.deviate d m) B d a :=
    mul_right_cancel₀ hma.ne' (by rw [hp]; ring)
  unfold refR1State condExp refR2Real Proc.deviatePure
  rw [hν', hp']

end c2b

end Cleanroom.Decision.DpReferentsCdt
