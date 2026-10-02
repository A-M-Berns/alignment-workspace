import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-bli-core` · WitnessGap: the correlated-points gap with full support, and the junk
sensitivity of the unguarded prior-optimality predicate (repair round 1; audit r1 adversarial
B1, N4)

Two variants of the correlated-points prior `corrPrior` (`WitnessCorr.lean`).

* **`gapPrior`** keeps the **correlation** and removes the **null mass**: `Ω = (state, point at
  T1, point at T2)`, state independent of the points, policy law `aa, bb ↦ 2/5`, `ab, ba ↦ 1/10`,
  home-only utilities `corrU`. Then `NDPOLICY`, `ReflectivePolicy` and a **non-vacuous**
  `LocalUtility` hold (every policy positive, `U` reads only the home point), so
  `exAnteValue = sepValue`; `NoCrossBranch` fails (`condEU T2 T1 true = 2/5 ≠ 8/5`), hence
  `IndependentPoints` fails; the one-step policy is `bb` (`EU T1: 7/10 < 4/5`; `EU T2: 2/5 <
  11/10`) with `exAnteValue bb = 1`, while `ab` is prior-optimal with `exAnteValue ab = 3/2`. So
  [[bli-program]] §3.9 U9(3)'s failure is a statement about `𝔼[U | pp = π]` of positive-mass
  policies after all: what it needs is correlation, not null mass (finding F-4, revised). This is
  also the N+ inhabitant of `ReflectivePolicy ∧ LocalUtility ∧ ¬ NoCrossBranch` (`corrPrior`
  inhabits `LocalUtility` only vacuously).
* **`corrPrior.shiftU (-2)`** — the correlated-points prior with every utility lowered by `2`
  (same masses, same points): nothing about the decision problem changes, `bb` is still best among
  the positive policies (`IsPriorOptimalOnSupport`, by `isPriorOptimalOnSupport_shiftU_iff`), yet
  the unguarded `IsPriorOptimal bb` **fails**, because the null policy `ab` scores the junk
  `0 > −1`. This is why `Corr.isPriorOptimal_bb` and clause 3 of `Lca.lca_refuted` are stated with
  the guarded predicate.

Promoted from the audit's probes `audit-r1-probes/GapFullSupport.lean` and
`audit-r1-probes/Vacuity.lean` (`PriorOptimalJunk`).
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-- Masses on `(state, point at T1, point at T2)`: state `1/2` each, policies `aa, bb ↦ 2/5`,
`ab, ba ↦ 1/10`.
Source: none: infrastructure (the full-support correlated law)
Kind: D
Fidelity: n/a -/
def gapMass : Fin 2 × Bool × Bool → ℚ := fun ω =>
  1 / 2 * (if ω.2.1 = ω.2.2 then 2 / 5 else 1 / 10)

/-- Home-only utility: `corrU` at the home point.
Source: [[bli-program]] §3.9(3) (the utilities of the correlated-points witness)
Kind: D
Fidelity: exact -/
def gapU : Fin 2 × Bool × Bool → ℚ := fun ω =>
  if ω.1 = 0 then corrU 0 ω.2.1 else corrU 1 ω.2.2

/-- **The full-support correlated prior**: the correlated-points witness with every policy of
positive mass (`tnPP` reads the two point coordinates).
Source: [[bli-program]] §3.9 U9(3); mandate T7 ("check what survives"); audit r1 adversarial N4
Kind: D
Fidelity: exact (correlation kept, null mass removed) -/
def gapPrior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool × Bool) gapMass
    (fun ω => by unfold gapMass; split_ifs <;> norm_num)
    (by unfold gapMass; simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]; norm_num)
    (fun ω => twoState ω.1) two_zeroOne tnPP gapU

namespace Gap

/-- `tnPP ω = π ↔` the two coordinates match `π`'s values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tnPP_eq_iff (ω : Fin 2 × Bool × Bool) (π : Policy twoTables Bool) :
    tnPP ω = π ↔ ω.2.1 = π T1 ∧ ω.2.2 = π T2 := by
  constructor
  · intro h; exact ⟨by rw [← h, TN.tnPP_T1], by rw [← h, TN.tnPP_T2]⟩
  · rintro ⟨h1, h2⟩
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl
    · rw [TN.tnPP_T1, h1]
    · rw [TN.tnPP_T2, h2]

/-- Policy masses: `2/5` for the constants, `1/10` otherwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_eq (π : Policy twoTables Bool) :
    gapPrior.policyMass π = if π T1 = π T2 then 2 / 5 else 1 / 10 := by
  unfold FiniteBLIPrior.policyMass gapPrior
  rw [handPrior_massOf]
  simp only [handPrior, tnPP_eq_iff]
  generalize π T1 = p₁
  generalize π T2 = p₂
  cases p₁ <;> cases p₂ <;>
    norm_num [massOf, gapMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]

/-- Cell masses: half the policy mass (the state is independent of the points).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_eq (T : ↥twoTables) (π : Policy twoTables Bool) :
    gapPrior.cellMass T π = 1 / 2 * (if π T1 = π T2 then 2 / 5 else 1 / 10) := by
  unfold FiniteBLIPrior.cellMass gapPrior
  rw [handPrior_massOf]
  simp only [handPrior, tnPP_eq_iff]
  rcases eq_T1_or_T2 T with rfl | rfl <;>
  · generalize π T1 = p₁
    generalize π T2 = p₂
    cases p₁ <;> cases p₂ <;>
      norm_num [massOf, gapMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
        T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]

/-- Cell values: the home utility at the home point.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellEU_eq (T : ↥twoTables) (π : Policy twoTables Bool) :
    gapPrior.cellEU T π = if T = T1 then corrU 0 (π T1) else corrU 1 (π T2) := by
  unfold FiniteBLIPrior.cellEU gapPrior
  rw [handPrior_condExp]
  simp only [handPrior, tnPP_eq_iff]
  rcases eq_T1_or_T2 T with rfl | rfl <;>
  · generalize π T1 = p₁
    generalize π T2 = p₂
    cases p₁ <;> cases p₂ <;>
      norm_num [condExp, massOf, integralOf, gapMass, gapU, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]

/-- Every state has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_eq (T : ↥twoTables) : gapPrior.stateMass T = 1 / 2 := by
  unfold FiniteBLIPrior.stateMass gapPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  rcases eq_T1_or_T2 T with rfl | rfl <;>
    norm_num [massOf, gapMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]

/-- **`NDPOLICY` holds**: every policy has positive mass.
Source: mandate T7 ("check what survives"); audit r1 adversarial N4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ndpolicy : gapPrior.NDPOLICY := by
  intro π; rw [policyMass_eq]; split_ifs <;> norm_num

/-- **`ReflectivePolicy` holds**: the state is independent of the policy.
Source: mandate T7; audit r1 adversarial N4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem reflectivePolicy : gapPrior.ReflectivePolicy := by
  intro T π _
  rw [cellMass_eq, policyMass_eq, stateMass_eq]
  split_ifs <;> norm_num

/-- **`LocalUtility` holds non-vacuously**: every cell is positive and the cell value is a
function of the home point. The N+ inhabitant of `ReflectivePolicy ∧ LocalUtility ∧
¬ NoCrossBranch` (`corrPrior`'s `LocalUtility` is N−).
Source: mandate T7; audit r1 adversarial N4, fidelity N6
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem localUtility : gapPrior.LocalUtility := by
  intro T π π' he _ _
  rw [cellEU_eq, cellEU_eq]
  rcases eq_T1_or_T2 T with rfl | rfl
  · simp [he]
  · simp [T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, he]

/-- The cross cell: `T2`'s value given `T1`'s point is `2/5` (point `true`) or `8/5` (`false`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condEU_T2_T1 (c : Bool) : gapPrior.condEU T2 T1 c = if c then 2 / 5 else 8 / 5 := by
  cases c <;>
  · unfold FiniteBLIPrior.condEU gapPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, gapMass, gapU, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, tnPP]

/-- The cross cells are positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_T2_T1_pos (c : Bool) : 0 < gapPrior.jointMass T2 T1 c := by
  cases c <;>
  · unfold FiniteBLIPrior.jointMass gapPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, gapMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, tnPP]

/-- **`NoCrossBranch` fails**: `T1`'s point moves `T2`'s expectation (`2/5 ≠ 8/5`).
Source: mandate T7; audit r1 adversarial N4
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem not_noCrossBranch : ¬ gapPrior.NoCrossBranch := by
  intro h
  have := h T1 T2 true false T2_ne_T1 (jointMass_T2_T1_pos true) (jointMass_T2_T1_pos false)
  rw [condEU_T2_T1, condEU_T2_T1] at this
  norm_num at this

/-- **`IndependentPoints` fails** (through the bridges: independence with `ReflectivePolicy` and
`LocalUtility` would give `NoCrossBranch`).
Source: mandate T7; audit r1 adversarial N4
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem not_independentPoints : ¬ gapPrior.IndependentPoints := fun hI =>
  not_noCrossBranch (gapPrior.noCrossBranch_of_localUtility_indepGivenState localUtility
    (gapPrior.indepGivenState_of_indep_reflectivePolicy hI reflectivePolicy))

/-- The home values: `T1 ↦ (1, 0)`, `T2 ↦ (0, 2)`.
Source: [[bli-program]] §3.9(3)
Kind: L
Fidelity: n/a -/
lemma homeEU_eq (T : ↥twoTables) (a : Bool) :
    gapPrior.homeEU T a = if T = T1 then (if a then 1 else 0) else (if a then 0 else 2) := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU gapPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, gapMass, gapU, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, tnPP]

/-- The one-step values: `T1 ↦ (7/10, 4/5)`, `T2 ↦ (2/5, 11/10)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EU_eq (T : ↥twoTables) (a : Bool) :
    gapPrior.EU T a =
      if T = T1 then (if a then 7 / 10 else 4 / 5) else (if a then 2 / 5 else 11 / 10) := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.EU gapPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, gapMass, gapU, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, tnPP]

/-- **The tiling failure in `exAnteValue`, with every policy of positive mass**: the one-step
policy is `bb` (value `1`), the prior-optimal policy is `ab` (value `3/2`), and `bb` is not
prior-optimal. U9(3)'s failure needs correlation, not null mass (finding F-4, revised).
Source: [[bli-program]] §3.9 U9(3); mandate T7; audit r1 adversarial N4
Kind: N+
Fidelity: exact (about `𝔼[U | pp = π]` of positive policies; no junk enters)
Hyps: (a) none -/
theorem gap_full_support :
    gapPrior.IsOneStepPolicy (fun _ => false) ∧ ¬ gapPrior.IsOneStepChoice T1 true ∧
      gapPrior.IsPriorOptimal abPol ∧ ¬ gapPrior.IsPriorOptimal (fun _ => false) ∧
      gapPrior.exAnteValue abPol = 3 / 2 ∧ gapPrior.exAnteValue (fun _ => false) = 1 := by
  have hupd : gapPrior.IsUpdatefulPolicy abPol := by
    intro T b
    rw [homeEU_eq, homeEU_eq]
    rcases eq_T1_or_T2 T with rfl | rfl
    · rw [abPol_T1]; cases b <;> norm_num
    · rw [abPol_T2]; cases b <;> norm_num [T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
  have hsep : ∀ π, gapPrior.exAnteValue π = gapPrior.sepValue π := fun π =>
    gapPrior.exAnteValue_eq_sepValue reflectivePolicy localUtility π (ndpolicy π)
  have hab : gapPrior.exAnteValue abPol = 3 / 2 := by
    rw [hsep]; unfold FiniteBLIPrior.sepValue
    rw [univ_twoTables, Finset.sum_pair T1_ne_T2]
    simp only [stateMass_eq, homeEU_eq, abPol_T1, abPol_T2, if_true, T2_ne_T1, if_false]
    norm_num
  have hbb : gapPrior.exAnteValue (fun _ => false) = 1 := by
    rw [hsep]; unfold FiniteBLIPrior.sepValue
    rw [univ_twoTables, Finset.sum_pair T1_ne_T2]
    simp only [stateMass_eq, homeEU_eq, if_true, T2_ne_T1, if_false, Bool.false_eq_true]
    norm_num
  refine ⟨fun T b => ?_, fun h => ?_,
    gapPrior.priorOptimal_of_updatefulPolicy ndpolicy reflectivePolicy localUtility abPol hupd,
    fun h => ?_, hab, hbb⟩
  · rw [EU_eq, EU_eq]; rcases eq_T1_or_T2 T with rfl | rfl <;> cases b <;>
      norm_num [T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
  · have := h false; rw [EU_eq, EU_eq] at this; norm_num at this
  · have := h abPol; rw [hab, hbb] at this; norm_num at this

end Gap

/-! ## The unguarded predicate is not shift-invariant on a prior with null policies -/

namespace Shift

/-- **Shifting `U` by `−2` breaks the unguarded `IsPriorOptimal` on the correlated-points prior**
while the guarded predicate survives: `exAnteValue aa = −3/2 < −1 = exAnteValue bb`, `ab` is
null with the junk value `0`, so `¬ IsPriorOptimal bb` (`0 > −1`) although
`IsPriorOptimalOnSupport bb`. Nothing about the decision problem changed. So `Corr.isPriorOptimal_bb`
must be, and is, stated with the guarded predicate.
Source: none: infrastructure (audit r1 adversarial B1, the shift test)
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem corrShift_junk :
    (corrPrior.shiftU (-2)).exAnteValue (fun _ => true) <
        (corrPrior.shiftU (-2)).exAnteValue (fun _ => false) ∧
      (corrPrior.shiftU (-2)).policyMass abPol = 0 ∧
      (corrPrior.shiftU (-2)).exAnteValue abPol = 0 ∧
      ¬ (corrPrior.shiftU (-2)).IsPriorOptimal (fun _ => false) ∧
      (corrPrior.shiftU (-2)).IsPriorOptimalOnSupport (fun _ => false) := by
  have hpos : ∀ c, 0 < corrPrior.policyMass (fun _ => c) := fun c => by
    rw [Corr.policyMass_const]; norm_num
  have hz : (corrPrior.shiftU (-2)).policyMass abPol = 0 := by
    rw [corrPrior.policyMass_shiftU]; exact Corr.policyMass_ab
  have haa := corrPrior.exAnteValue_shiftU (-2) (fun _ => true) (hpos true)
  have hbb := corrPrior.exAnteValue_shiftU (-2) (fun _ => false) (hpos false)
  rw [Corr.exAnteValue_const] at haa hbb
  simp only [if_true, Bool.false_eq_true, if_false] at haa hbb
  refine ⟨?_, hz, exAnteValue_eq_zero_of_null _ _ hz, ?_, ?_⟩
  · rw [haa, hbb]; norm_num
  · intro h
    have := h abPol
    rw [hbb, exAnteValue_eq_zero_of_null _ _ hz] at this
    norm_num at this
  · exact (corrPrior.isPriorOptimalOnSupport_shiftU_iff (-2) _ (hpos false)).mpr
      Corr.isPriorOptimal_bb

end Shift

end Cleanroom.Bli.UdtBliCore
