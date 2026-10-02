import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-bli-core` · WitnessXor: the both-rules-indifferent extreme of the point-level package
(repair round 1; audit r1 fidelity B1; regraded in repair round 2, audit r2 fidelity B1 =
adversarial B1)

[[bli-program]] §3.9 U4 states Good's theorem under the **point-level** package
`Reflective ∧ NoCrossBranch`. The package's `good` needs the **policy-level**
`ReflectivePolicy ∧ LocalUtility` instead (`Good.lean`). This module's prior inhabits the full
point-level package with full positivity and shows that `exAnteValue ≠ sepValue` there — the
identification of the program's array formula with the ex-ante value of actual policies fails
(`Xor.exAnteValue_ne_sepValue`, tie-independent, N+). It is **not** the refutation of record for
U4's gloss: that is the tie-free prior of `WitnessTieFree.lean` (`TieFree.good_fails_pointLevel`).

`xorPrior`: two tables of mass `1/2`, independent fair points at both, utility `1` on `T1` iff
the two points **agree**, `0` on `T2`. Then

* `Reflective`, `NoCrossBranch`, `NDPOL`, `NDHOME`, `NDPOLICY` all hold (every policy has mass
  `1/4`; `T2`'s value is `0` whatever `T1`'s point, and `T1`'s value given `T2`'s point is `1/2`
  for both values);
* **both rules are totally indifferent**: every home value is `1/2` at `T1` and `0` at `T2`
  (`homeEU_eq`), every one-step value is `1/4` (`EU_eq`); so every policy is updateful
  (`every_policy_updateful`) and every policy is one-step (`every_policy_oneStep`);
* the tied maximizer `ab` has `exAnteValue ab = 0 < 1/2 = exAnteValue (const true)` and is not
  prior-optimal (`good_fails_pointLevel`) — but the tied maximizers `aa`, `bb` *are* the constant
  policies and attain `1/2`, so a tie-break toward either rescues "deferral weakly dominates every
  precommitment". What this prior refutes is the **∀-form** — every updateful policy weakly
  dominates every constant policy, the conclusion of the package's `good` — under the point-level
  package; it does not refute the gloss for the rule's choice under an argmax *function* (the
  program's §2.8 `oneStepUDT`/`updateful`). Hence `good_fails_pointLevel` is graded **N−** as a
  refutation of U4 (both round-2 audits), and the tie-free prior carries the refutation of record;
* `exAnteValue (const true) = 1/2 ≠ 1/4 = sepValue (const true)` on a positive policy (N+);
* `LocalUtility` fails (the cells `state = T1 ∧ pp = aa` and `state = T1 ∧ pp = ab` have values
  `1` and `0`).

(The correlated-points prior `corrPrior`, cited for this in the first version of F-2, does not
witness the point-level insufficiency: it is not `NoCrossBranch`, and on its positive policies
`exAnteValue = sepValue` holds. It witnesses the converse gap.)

Promoted from the audit's probe `audit-r1-probes/PointLevelGoodFails.lean`.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-- Uniform mass `1/8` on `(state, point at T1, point at T2)`.
Source: none: infrastructure (the XOR prior's base law)
Kind: D
Fidelity: n/a -/
def xorMass : Fin 2 × Bool × Bool → ℚ := fun _ => 1 / 8

/-- The policy points of the XOR prior: coordinate 1 at `T1`, coordinate 2 at `T2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def xorPP (ω : Fin 2 × Bool × Bool) : Policy twoTables Bool :=
  fun T => if T = T1 then ω.2.1 else ω.2.2

/-- The XOR utility: `1` on `T1` iff the two points agree; `0` on `T2`.
Source: none: infrastructure (chosen so that `T1`'s value reads the *other* branch's point)
Kind: D
Fidelity: n/a -/
def xorU : Fin 2 × Bool × Bool → ℚ := fun ω =>
  if ω.1 = 0 then (if ω.2.1 = ω.2.2 then 1 else 0) else 0

/-- **The XOR prior**: two tables of mass `1/2`, independent fair points, utility `xorU`.
Source: [[bli-program]] §3.9 U4 (the hypothesis package it states); audit r1 fidelity B1
Kind: D
Fidelity: exact (a `FiniteBLIPrior` inhabiting U4's package with full positivity) -/
def xorPrior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool × Bool) xorMass (fun _ => by norm_num [xorMass])
    (by norm_num [xorMass, Finset.sum_const, Finset.card_univ])
    (fun ω => twoState ω.1) two_zeroOne xorPP xorU

namespace Xor

/-- `xorPP ω T1 = ω.2.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma xorPP_T1 (ω : Fin 2 × Bool × Bool) : xorPP ω T1 = ω.2.1 := by simp [xorPP]

/-- `xorPP ω T2 = ω.2.2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma xorPP_T2 (ω : Fin 2 × Bool × Bool) : xorPP ω T2 = ω.2.2 := by
  simp [xorPP, Ne.symm mAsk_ne_mRec]

/-- A policy is determined by its two values: `xorPP ω = xorPP (0, b, c) ↔ ω.2 = (b, c)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma xorPP_eq_iff (ω : Fin 2 × Bool × Bool) (b c : Bool) :
    (xorPP ω = xorPP (0, b, c)) ↔ (ω.2.1 = b ∧ ω.2.2 = c) := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h T1, by simpa using congrFun h T2⟩
  · rintro ⟨h1, h2⟩
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl <;> simp [h1, h2]

/-- Every policy is `xorPP (0, π T1, π T2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policy_eq_xorPP (π : Policy twoTables Bool) : π = xorPP (0, π T1, π T2) := by
  funext T
  rcases eq_T1_or_T2 T with rfl | rfl <;> simp

/-- Every state has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_eq (T : ↥twoTables) : xorPrior.stateMass T = 1 / 2 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;>
  · unfold FiniteBLIPrior.stateMass xorPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, xorMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- Every point has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_eq (T : ↥twoTables) (a : Bool) : xorPrior.ppMass T a = 1 / 2 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.ppMass xorPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, xorMass, xorPP, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- Every joint cell `state = T' ∧ pp · T = a` has mass `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_eq (T' T : ↥twoTables) (a : Bool) : xorPrior.jointMass T' T a = 1 / 4 := by
  rcases eq_T1_or_T2 T' with rfl | rfl <;> rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.jointMass xorPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, xorMass, xorPP, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- **`Reflective` holds**: the points are independent of the state.
Source: [[bli-program]] §3.9 U4 (its first hypothesis); audit r1 fidelity B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem reflective : xorPrior.Reflective := by
  intro T T' a _
  unfold FiniteBLIPrior.branchProb
  rw [jointMass_eq, ppMass_eq, stateMass_eq]
  norm_num

/-- The cross cells: `T2`'s value is `0` whatever `T1`'s point; `T1`'s value given `T2`'s point is
`1/2` for both values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condEU_cross (a : Bool) :
    xorPrior.condEU T2 T1 a = 0 ∧ xorPrior.condEU T1 T2 a = 1 / 2 := by
  cases a <;>
  · constructor <;>
    · unfold FiniteBLIPrior.condEU xorPrior
      rw [handPrior_condExp]
      simp only [handPrior]
      norm_num [condExp, massOf, integralOf, xorMass, xorU, xorPP, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec,
        mAsk_ne_mRec]

/-- **`NoCrossBranch` holds**: neither point moves the other branch's expectation.
Source: [[bli-program]] §3.9 U4 (its second hypothesis); audit r1 fidelity B1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem noCrossBranch : xorPrior.NoCrossBranch := by
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
lemma policyMass_eq (π : Policy twoTables Bool) : xorPrior.policyMass π = 1 / 4 := by
  rw [policy_eq_xorPP π]
  unfold FiniteBLIPrior.policyMass xorPrior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, xorPP_eq_iff]
  cases π T1 <;> cases π T2 <;>
  · norm_num [xorMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]

/-- **Full positivity**: `NDPOL`, `NDHOME`, `NDPOLICY` all hold.
Source: audit r1 fidelity B1 (the refutation is not a null-mass artifact)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem positivity_all : xorPrior.NDPOL ∧ xorPrior.NDHOME ∧ xorPrior.NDPOLICY := by
  refine ⟨fun T a => ?_, fun T a => ?_, fun π => ?_⟩
  · rw [ppMass_eq]; norm_num
  · rw [jointMass_eq]; norm_num
  · rw [policyMass_eq]; norm_num

/-- The home values: `1/2` at `T1` for both actions, `0` at `T2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma homeEU_eq (T : ↥twoTables) (a : Bool) :
    xorPrior.homeEU T a = if T = T1 then 1 / 2 else 0 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU xorPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, xorMass, xorU, xorPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec,
      mAsk_ne_mRec]

/-- Every policy is updateful (all home values tie).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem every_policy_updateful (π : Policy twoTables Bool) : xorPrior.IsUpdatefulPolicy π := by
  intro T b
  rw [homeEU_eq, homeEU_eq]

/-- The one-step values: `1/4` at every table for every action (`EU T1 a = μ(T1)·μ(pp·T2 = a)`,
`EU T2 a = μ(T1)·μ(pp·T1 = a)`). The one-step rule is as indifferent as the updateful one.
Source: none: infrastructure (audit r2 fidelity non-blocking 5, adversarial B1)
Kind: L
Fidelity: n/a -/
lemma EU_eq (T : ↥twoTables) (a : Bool) : xorPrior.EU T a = 1 / 4 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.EU xorPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, xorMass, xorU, xorPP, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec,
      mAsk_ne_mRec]

/-- Every policy is one-step (all one-step values tie): both rules are totally indifferent on
this prior, which is why it cannot carry the refutation of record (see `WitnessTieFree.lean`).
Source: none: infrastructure (audit r2 adversarial B1)
Kind: L
Fidelity: n/a -/
theorem every_policy_oneStep (π : Policy twoTables Bool) : xorPrior.IsOneStepPolicy π := by
  intro T b
  rw [EU_eq, EU_eq]

/-- The ex-ante values: `const true ↦ 1/2`, `ab ↦ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exAnteValue_vals :
    xorPrior.exAnteValue (fun _ => true) = 1 / 2 ∧ xorPrior.exAnteValue abPol = 0 := by
  have hab : abPol = xorPP (0, true, false) := by
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl <;> simp
  have hc : (fun _ : ↥twoTables => true) = xorPP (0, true, true) := by
    funext T
    rcases eq_T1_or_T2 T with rfl | rfl <;> simp
  rw [hab, hc]
  constructor <;>
  · unfold FiniteBLIPrior.exAnteValue xorPrior
    rw [handPrior_condExp]
    simp only [handPrior, condExp, massOf, integralOf, xorPP_eq_iff]
    norm_num [xorMass, xorU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]

/-- **`exAnteValue ≠ sepValue` on a positive policy under the full point-level package**:
`exAnteValue (const true) = 1/2` while `sepValue (const true) = 1/4`.
Source: [[bli-program]] §3.9 U4 (the identification of its two sides with `exAnteValue`);
finding F-2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exAnteValue_ne_sepValue :
    xorPrior.exAnteValue (fun _ => true) = 1 / 2 ∧
      xorPrior.sepValue (fun _ => true) = 1 / 4 ∧
      0 < xorPrior.policyMass (fun _ => true) := by
  refine ⟨exAnteValue_vals.1, ?_, by rw [policyMass_eq]; norm_num⟩
  unfold FiniteBLIPrior.sepValue
  rw [univ_twoTables, Finset.sum_pair T1_ne_T2]
  simp only [stateMass_eq, homeEU_eq, if_true, T2_ne_T1, if_false]
  norm_num

/-- **The ∀-form of Good's conclusion fails under `Reflective ∧ NoCrossBranch` and full
positivity**: the updateful policy `ab` (positive mass `1/4`) is strictly beaten by the constant
policy `true`, and is not prior-optimal. `ab` is updateful *by tie only* (every policy is
updateful and one-step here, `every_policy_updateful`, `every_policy_oneStep`), and the tied
maximizers `aa`, `bb` attain the best constant value `1/2`; so this refutes "every updateful
policy weakly dominates every constant policy" (the conclusion of `good`) under the point-level
package, not [[bli-program]] §3.9 U4's gloss for the rule's choice under an argmax function. The
refutation of record for that gloss is `TieFree.good_fails_pointLevel` (`WitnessTieFree.lean`),
where the rule has one choice and both constants beat it.
Source: [[bli-program]] §3.9 U4; finding F-2; audit r1 fidelity B1; regraded by audit r2
fidelity B1 = adversarial B1
Kind: N−
Fidelity: weaker: refutes the ∀-form only; as a refutation of U4's gloss it is tie-dependent
(both rules totally indifferent), the degenerate extreme of the point-level package
Hyps: (a) none -/
theorem good_fails_pointLevel :
    xorPrior.Reflective ∧ xorPrior.NoCrossBranch ∧
      xorPrior.NDPOL ∧ xorPrior.NDHOME ∧ xorPrior.NDPOLICY ∧
      xorPrior.IsUpdatefulPolicy abPol ∧ 0 < xorPrior.policyMass abPol ∧
      0 < xorPrior.policyMass (fun _ => true) ∧
      xorPrior.exAnteValue abPol < xorPrior.exAnteValue (fun _ => true) ∧
      ¬ xorPrior.IsPriorOptimal abPol := by
  obtain ⟨h1, h2, h3⟩ := positivity_all
  refine ⟨reflective, noCrossBranch, h1, h2, h3, every_policy_updateful abPol,
    by rw [policyMass_eq]; norm_num, by rw [policyMass_eq]; norm_num, ?_, ?_⟩
  · rw [exAnteValue_vals.1, exAnteValue_vals.2]; norm_num
  · intro h
    have := h (fun _ => true)
    rw [exAnteValue_vals.1, exAnteValue_vals.2] at this
    norm_num at this

/-- Every cell `state = T1 ∧ pp = π` is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_T1_pos (π : Policy twoTables Bool) : 0 < xorPrior.cellMass T1 π := by
  rw [policy_eq_xorPP π]
  unfold FiniteBLIPrior.cellMass xorPrior
  rw [handPrior_massOf]
  simp only [handPrior, massOf, xorPP_eq_iff]
  cases π T1 <;> cases π T2 <;>
  · norm_num [xorMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2,
      T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- The cell values at `T1`: `1` if the two points agree, `0` otherwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellEU_T1 (b c : Bool) : xorPrior.cellEU T1 (xorPP (0, b, c)) = if b = c then 1 else 0 := by
  unfold FiniteBLIPrior.cellEU xorPrior
  rw [handPrior_condExp]
  simp only [handPrior, condExp, massOf, integralOf, xorPP_eq_iff]
  cases b <;> cases c <;>
  · norm_num [xorMass, xorU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- **`LocalUtility` fails** (as it must, since `good` would otherwise apply): the cells
`state = T1 ∧ pp = aa` and `state = T1 ∧ pp = ab` agree at `T1` and have values `1` and `0`.
Source: finding F-2 (the hypothesis U4 is missing); audit r1 fidelity B1
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem not_localUtility : ¬ xorPrior.LocalUtility := by
  intro h
  have := h T1 (xorPP (0, true, true)) (xorPP (0, true, false)) (by simp) (cellMass_T1_pos _)
    (cellMass_T1_pos _)
  rw [cellEU_T1, cellEU_T1] at this
  norm_num at this

end Xor

end Cleanroom.Bli.UdtBliCore
