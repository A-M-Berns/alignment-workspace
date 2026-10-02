import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-bli-core` · WitnessTieFree: the refutation of record for [[bli-program]] §3.9 U4's gloss,
tie-free (repair round 2; audit r2 fidelity B1 = adversarial B1)

[[bli-program]] §3.9 U4 states Good's theorem under the **point-level** package
`Reflective ∧ NoCrossBranch`, and glosses its displayed inequality as "deferring to the one-step
(= updateful) rule weakly dominates every precommitted action". The package's `good` needs the
**policy-level** `ReflectivePolicy ∧ LocalUtility` instead (`Good.lean`). Repair round 1's witness
for the necessity of that substitution, `xorPrior` (`WitnessXor.lean`), refutes only the ∀-form
("*every* updateful policy weakly dominates every constant policy"): there both rules are totally
indifferent, so the beaten policy is updateful by tie alone and a tie-break toward `aa` or `bb`
rescues deferral. Both round-2 audits found this; this module is the tie-free witness they asked
for (the fidelity audit's two-table probe, `audit-r2-probes/TieFreeGoodFails.lean`, promoted).

`tfPrior`: two tables of mass `1/2`, independent fair points, utility on `T1` a function
`f(pp·T1, pp·T2)` with `f = [[4, 1], [0, 3]]` (rows: point at `T1` = `true`/`false`; columns:
point at `T2` = `true`/`false`), utility on `T2` = `g(pp·T2)` with `g true = 1`, `g false = 2`.
Then

* `Reflective` (the points are independent of the state), `NoCrossBranch` (equal column sums of
  `f`, `4 + 0 = 1 + 3`, make `T1`'s expectation given `T2`'s point `2` either way; `T2`'s value
  given `T1`'s point is `3/2` either way), `NDPOL`, `NDHOME`, `NDPOLICY` (every cell `1/4`);
* home values `5/2 > 3/2` at `T1` and `1 < 2` at `T2`: `ab = (true, false)` is the **unique**
  updateful policy; one-step values `2 > 3/2` at `T1` and `3/2 < 2` at `T2`: `ab` is the
  **unique** one-step policy (T5 in action);
* `exAnteValue ab = 3/2`, and **both** constant policies have `exAnteValue = 5/2`: every
  precommitment strictly beats the rule's only choice, and `¬ IsPriorOptimal ab`;
* `sepValue ab = 9/4 ≠ 3/2 = exAnteValue ab` on a positive policy; `LocalUtility` fails.

So the refuted statement is U4's gloss — "deferring to the one-step (= updateful) rule weakly
dominates every precommitted action", read about `exAnteValue` of the rule's choice — under
`Reflective ∧ NoCrossBranch` with full positivity, **whatever the tie-break**, because there is no
tie. U4's displayed inequality `∑_T μ(T) max_a 𝔼[U | T, a] ≥ max_a ∑_T μ(T) 𝔼[U | T, a]` is a
true identity on every prior, and here it reads `sepValue ab = 9/4 ≥ 7/4 = sepValue (const c)`
(`sepValue_vals`, `exAnteValue_ne_sepValue`) — the array comparison goes the way U4 says while the
ex-ante comparison (`3/2 < 5/2`) goes the other way. What fails is the identification of the
array's entries with `exAnteValue` of actual policies, exactly the step `good` takes through
`LocalUtility` (finding F-2, restated).
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-- Uniform mass `1/8` on `(state, point at T1, point at T2)`.
Source: none: infrastructure (the tie-free prior's base law)
Kind: D
Fidelity: n/a -/
def tfMass : Fin 2 × Bool × Bool → ℚ := fun _ => 1 / 8

/-- The policy points of the tie-free prior: coordinate 1 at `T1`, coordinate 2 at `T2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tfPP (ω : Fin 2 × Bool × Bool) : Policy twoTables Bool :=
  fun T => if T = T1 then ω.2.1 else ω.2.2

/-- The tie-free utility: `f = [[4, 1], [0, 3]]` of `(pp·T1, pp·T2)` on `T1`; `g = (1, 2)` of
`pp·T2` on `T2`. The equal column sums of `f` are what make `NoCrossBranch` hold while `T1`'s
value reads the other branch's point.
Source: none: infrastructure (audit r2 fidelity B1's construction)
Kind: D
Fidelity: n/a -/
def tfU : Fin 2 × Bool × Bool → ℚ := fun ω =>
  if ω.1 = 0 then
    (if ω.2.1 then (if ω.2.2 then 4 else 1) else (if ω.2.2 then 0 else 3))
  else (if ω.2.2 then 1 else 2)

/-- **The tie-free prior**: two tables of mass `1/2`, independent fair points, utility `tfU`.
Source: [[bli-program]] §3.9 U4 (the hypothesis package it states); audit r2 fidelity B1,
adversarial B1
Kind: D
Fidelity: exact (a `FiniteBLIPrior` inhabiting U4's package with full positivity and no ties) -/
def tfPrior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool × Bool) tfMass (fun _ => by norm_num [tfMass])
    (by norm_num [tfMass, Finset.sum_const, Finset.card_univ])
    (fun ω => twoState ω.1) two_zeroOne tfPP tfU

namespace TieFree

/-- `tfPP ω T1 = ω.2.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tfPP_T1 (ω : Fin 2 × Bool × Bool) : tfPP ω T1 = ω.2.1 := by simp [tfPP]

/-- `tfPP ω T2 = ω.2.2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tfPP_T2 (ω : Fin 2 × Bool × Bool) : tfPP ω T2 = ω.2.2 := by
  simp [tfPP, Ne.symm mAsk_ne_mRec]

/-- A policy is determined by its two values: `tfPP ω = tfPP (0, b, c) ↔ ω.2 = (b, c)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tfPP_eq_iff (ω : Fin 2 × Bool × Bool) (b c : Bool) :
    (tfPP ω = tfPP (0, b, c)) ↔ (ω.2.1 = b ∧ ω.2.2 = c) := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h T1, by simpa using congrFun h T2⟩
  · rintro ⟨h1, h2⟩
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl <;> simp [h1, h2]

/-- Every policy is `tfPP (0, π T1, π T2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policy_eq_tfPP (π : Policy twoTables Bool) : π = tfPP (0, π T1, π T2) := by
  funext T
  rcases eq_T1_or_T2 T with rfl | rfl <;> simp

/-- Every state has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_eq (T : ↥twoTables) : tfPrior.stateMass T = 1 / 2 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;>
  · unfold FiniteBLIPrior.stateMass tfPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, tfMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- Every point has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_eq (T : ↥twoTables) (a : Bool) : tfPrior.ppMass T a = 1 / 2 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.ppMass tfPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, tfMass, tfPP, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- Every joint cell `state = T' ∧ pp · T = a` has mass `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_eq (T' T : ↥twoTables) (a : Bool) : tfPrior.jointMass T' T a = 1 / 4 := by
  rcases eq_T1_or_T2 T' with rfl | rfl <;> rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.jointMass tfPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, tfMass, tfPP, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- **`Reflective` holds**: the points are independent of the state.
Source: [[bli-program]] §3.9 U4 (its first hypothesis); audit r2 fidelity B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem reflective : tfPrior.Reflective := by
  intro T T' a _
  unfold FiniteBLIPrior.branchProb
  rw [jointMass_eq, ppMass_eq, stateMass_eq]
  norm_num

/-- The cross cells: `T2`'s value given `T1`'s point is `3/2` either way; `T1`'s value given
`T2`'s point is `2` either way (equal column sums of `f`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condEU_cross (a : Bool) :
    tfPrior.condEU T2 T1 a = 3 / 2 ∧ tfPrior.condEU T1 T2 a = 2 := by
  cases a <;>
  · constructor <;>
    · unfold FiniteBLIPrior.condEU tfPrior
      rw [handPrior_condExp]
      simp only [handPrior]
      norm_num [condExp, massOf, integralOf, tfMass, tfU, tfPP, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec,
        mAsk_ne_mRec]

/-- **`NoCrossBranch` holds** (the program's §2.8 invariance form, which is `Defs.lean`'s):
neither point moves the other branch's expectation, although `T1`'s utility *reads* `T2`'s point.
Source: [[bli-program]] §3.9 U4 (its second hypothesis); audit r2 fidelity B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem noCrossBranch : tfPrior.NoCrossBranch := by
  intro T T' a b hne _ _
  rcases eq_T1_or_T2 T with rfl | rfl <;> rcases eq_T1_or_T2 T' with rfl | rfl
  · exact absurd rfl hne
  · rw [(condEU_cross a).1, (condEU_cross b).1]
  · rw [(condEU_cross a).2, (condEU_cross b).2]
  · exact absurd rfl hne

/-- Every policy has mass `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_eq (π : Policy twoTables Bool) : tfPrior.policyMass π = 1 / 4 := by
  rw [policy_eq_tfPP π]
  unfold FiniteBLIPrior.policyMass tfPrior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, tfPP_eq_iff]
  cases π T1 <;> cases π T2 <;>
  · norm_num [tfMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]

/-- **Full positivity**: `NDPOL`, `NDHOME`, `NDPOLICY` all hold.
Source: audit r2 fidelity B1 (the refutation is not a null-mass artifact)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem positivity_all : tfPrior.NDPOL ∧ tfPrior.NDHOME ∧ tfPrior.NDPOLICY := by
  refine ⟨fun T a => ?_, fun T a => ?_, fun π => ?_⟩
  · rw [ppMass_eq]; norm_num
  · rw [jointMass_eq]; norm_num
  · rw [policyMass_eq]; norm_num

/-- Home values: `T1 ↦ (5/2, 3/2)`, `T2 ↦ (1, 2)` — no tie at either table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma homeEU_eq (T : ↥twoTables) (a : Bool) :
    tfPrior.homeEU T a =
      if T = T1 then (if a then 5 / 2 else 3 / 2) else (if a then 1 else 2) := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU tfPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tfMass, tfU, tfPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec,
      mAsk_ne_mRec]

/-- One-step values: `T1 ↦ (2, 3/2)`, `T2 ↦ (3/2, 2)` — no tie at either table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EU_eq (T : ↥twoTables) (a : Bool) :
    tfPrior.EU T a =
      if T = T1 then (if a then 2 else 3 / 2) else (if a then 3 / 2 else 2) := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.EU tfPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tfMass, tfU, tfPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec,
      mAsk_ne_mRec]

/-- **`ab` is the unique updateful policy**: it is updateful, and every updateful policy is `ab`.
Source: audit r2 fidelity B1 (no tie for the updateful rule)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem updateful_unique :
    tfPrior.IsUpdatefulPolicy abPol ∧ ∀ π, tfPrior.IsUpdatefulPolicy π → π = abPol := by
  constructor
  · intro T b
    rw [homeEU_eq, homeEU_eq]
    rcases eq_T1_or_T2 T with rfl | rfl
    · rw [abPol_T1]; cases b <;> norm_num
    · rw [abPol_T2]; cases b <;> norm_num [T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
  · intro π h
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl
    · have h1 := h T1 true
      rw [homeEU_eq, homeEU_eq] at h1
      rw [abPol_T1]
      cases hπ : π T1
      · rw [hπ] at h1; norm_num at h1
      · rfl
    · have h2 := h T2 false
      rw [homeEU_eq, homeEU_eq] at h2
      rw [abPol_T2]
      cases hπ : π T2
      · rfl
      · rw [hπ] at h2; norm_num [T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec] at h2

/-- **`ab` is the unique one-step policy** (T5 in action: the two rules agree on one choice).
Source: audit r2 fidelity B1 (no tie for the one-step rule); [[bli-program]] §3.9 U3
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem oneStep_unique :
    tfPrior.IsOneStepPolicy abPol ∧ ∀ π, tfPrior.IsOneStepPolicy π → π = abPol := by
  constructor
  · intro T b
    rw [EU_eq, EU_eq]
    rcases eq_T1_or_T2 T with rfl | rfl
    · rw [abPol_T1]; cases b <;> norm_num
    · rw [abPol_T2]; cases b <;> norm_num [T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
  · intro π h
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl
    · have h1 := h T1 true
      rw [EU_eq, EU_eq] at h1
      rw [abPol_T1]
      cases hπ : π T1
      · rw [hπ] at h1; norm_num at h1
      · rfl
    · have h2 := h T2 false
      rw [EU_eq, EU_eq] at h2
      rw [abPol_T2]
      cases hπ : π T2
      · rfl
      · rw [hπ] at h2; norm_num [T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec] at h2

/-- Ex-ante values: `ab ↦ 3/2`, both constants `↦ 5/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exAnteValue_vals :
    tfPrior.exAnteValue abPol = 3 / 2 ∧
      tfPrior.exAnteValue (fun _ => true) = 5 / 2 ∧
      tfPrior.exAnteValue (fun _ => false) = 5 / 2 := by
  have hab : abPol = tfPP (0, true, false) := by
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl <;> simp
  have ht : (fun _ : ↥twoTables => true) = tfPP (0, true, true) := by
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl <;> simp
  have hf : (fun _ : ↥twoTables => false) = tfPP (0, false, false) := by
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl <;> simp
  rw [hab, ht, hf]
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold FiniteBLIPrior.exAnteValue tfPrior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, tfPP_eq_iff]
    norm_num [tfMass, tfU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]

/-- **The refutation of record, tie-free**: under `Reflective ∧ NoCrossBranch` and full
positivity, the unique updateful (= unique one-step) policy `ab` has ex-ante value `3/2`, and
**every** constant policy has ex-ante value `5/2`; so `ab` is not prior-optimal. This refutes
[[bli-program]] §3.9 U4's gloss — "deferring to the one-step (= updateful) rule weakly dominates
every precommitted action", read about `𝔼[U | pp = π]` of the rule's choice — under U4's stated
point-level hypotheses with full positivity, for every tie-break (there is no tie). U4's displayed
max-of-sums inequality stays true; the honest statement of the gloss is `good` under
`ReflectivePolicy ∧ LocalUtility`.
Source: [[bli-program]] §3.9 U4; finding F-2 (restated); audit r2 fidelity B1, adversarial B1
Kind: N+
Fidelity: exact (U4's hypothesis package inhabited with full positivity; its gloss false for the
unique updateful = unique one-step policy against both constants)
Hyps: (a) none -/
theorem good_fails_pointLevel :
    tfPrior.Reflective ∧ tfPrior.NoCrossBranch ∧
      tfPrior.NDPOL ∧ tfPrior.NDHOME ∧ tfPrior.NDPOLICY ∧
      tfPrior.IsUpdatefulPolicy abPol ∧ (∀ π, tfPrior.IsUpdatefulPolicy π → π = abPol) ∧
      tfPrior.IsOneStepPolicy abPol ∧ (∀ π, tfPrior.IsOneStepPolicy π → π = abPol) ∧
      tfPrior.exAnteValue abPol = 3 / 2 ∧
      (∀ c, tfPrior.exAnteValue (fun _ => c) = 5 / 2) ∧
      (∀ c, tfPrior.exAnteValue abPol < tfPrior.exAnteValue (fun _ => c)) ∧
      ¬ tfPrior.IsPriorOptimal abPol := by
  obtain ⟨h1, h2, h3⟩ := positivity_all
  obtain ⟨hu, huq⟩ := updateful_unique
  obtain ⟨ho, hoq⟩ := oneStep_unique
  obtain ⟨vab, vt, vf⟩ := exAnteValue_vals
  have hc : ∀ c, tfPrior.exAnteValue (fun _ => c) = 5 / 2 := by
    intro c; cases c
    · exact vf
    · exact vt
  refine ⟨reflective, noCrossBranch, h1, h2, h3, hu, huq, ho, hoq, vab, hc, ?_, ?_⟩
  · intro c; rw [vab, hc]; norm_num
  · intro h
    have := h (fun _ => true)
    rw [vab, vt] at this
    norm_num at this

/-- The separable values: `sepValue ab = 9/4`, `sepValue (const c) = 7/4` for both `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sepValue_vals :
    tfPrior.sepValue abPol = 9 / 4 ∧ ∀ c, tfPrior.sepValue (fun _ => c) = 7 / 4 := by
  constructor
  · unfold FiniteBLIPrior.sepValue
    rw [univ_twoTables, Finset.sum_pair T1_ne_T2]
    simp only [stateMass_eq, homeEU_eq, abPol_T1, abPol_T2, if_true, T2_ne_T1, if_false]
    norm_num
  · intro c
    unfold FiniteBLIPrior.sepValue
    rw [univ_twoTables, Finset.sum_pair T1_ne_T2]
    simp only [stateMass_eq, homeEU_eq, if_true, T2_ne_T1, if_false]
    cases c <;> norm_num

/-- **`exAnteValue ≠ sepValue` on positive policies under the full point-level package, and the
array inequality holds while the gloss fails**: `exAnteValue ab = 3/2 ≠ 9/4 = sepValue ab`,
`exAnteValue (const c) = 5/2 ≠ 7/4 = sepValue (const c)`; the array comparison
`sepValue ab = 9/4 ≥ 7/4 = sepValue (const c)` goes the way U4's displayed inequality says, and
the ex-ante comparison goes the other way.
Source: [[bli-program]] §3.9 U4 (the identification of its two sides with `exAnteValue`);
finding F-2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exAnteValue_ne_sepValue :
    tfPrior.exAnteValue abPol ≠ tfPrior.sepValue abPol ∧
      (∀ c, tfPrior.exAnteValue (fun _ => c) ≠ tfPrior.sepValue (fun _ => c)) ∧
      (∀ c, tfPrior.sepValue (fun _ => c) ≤ tfPrior.sepValue abPol) ∧
      (∀ c, tfPrior.exAnteValue abPol < tfPrior.exAnteValue (fun _ => c)) := by
  obtain ⟨vab, vt, vf⟩ := exAnteValue_vals
  obtain ⟨sab, sc⟩ := sepValue_vals
  have hc : ∀ c, tfPrior.exAnteValue (fun _ => c) = 5 / 2 := by
    intro c; cases c
    · exact vf
    · exact vt
  refine ⟨by rw [vab, sab]; norm_num, fun c => by rw [hc, sc]; norm_num,
    fun c => by rw [sc, sab]; norm_num, fun c => by rw [vab, hc]; norm_num⟩

/-- Every cell `state = T1 ∧ pp = π` is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_T1_pos (π : Policy twoTables Bool) : 0 < tfPrior.cellMass T1 π := by
  rw [policy_eq_tfPP π]
  unfold FiniteBLIPrior.cellMass tfPrior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, tfPP_eq_iff]
  cases π T1 <;> cases π T2 <;>
  · norm_num [tfMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2,
      T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- The cell values at `T1`: `f (b, c)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellEU_T1 (b c : Bool) :
    tfPrior.cellEU T1 (tfPP (0, b, c)) =
      if b then (if c then 4 else 1) else (if c then 0 else 3) := by
  unfold FiniteBLIPrior.cellEU tfPrior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, tfPP_eq_iff]
  cases b <;> cases c <;>
  · norm_num [tfMass, tfU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- **`LocalUtility` fails** (as it must, since `good` would otherwise apply): the cells
`state = T1 ∧ pp = aa` and `state = T1 ∧ pp = ab` agree at `T1` and have values `4` and `1`.
Source: finding F-2 (the hypothesis U4 is missing); audit r2 fidelity B1
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem not_localUtility : ¬ tfPrior.LocalUtility := by
  intro h
  have := h T1 (tfPP (0, true, true)) (tfPP (0, true, false)) (by simp) (cellMass_T1_pos _)
    (cellMass_T1_pos _)
  rw [cellEU_T1, cellEU_T1] at this
  norm_num at this

end TieFree

end Cleanroom.Bli.UdtBliCore
