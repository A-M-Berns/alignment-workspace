import Cleanroom.Bli.UdtBliCore.Bridges
import Cleanroom.Bli.UdtBliCore.Mugging

/-!
# `udt-bli-core` · WitnessCorr: the gap witnesses for the two-level bridges (T7, N+/N−)

Three hand-built priors over the two tables `T1 = Ask = (1, 0)`, `T2 = Rec = (0, 1)`:

* **`corrPrior`** — the correlated-points prior of [[bli-program]] §3.9(3): two tables of mass
  `1/2`, policy points perfectly correlated (`aa` or `bb`, mass `1/2` each), utilities
  `U(T1, a) = 1, U(T1, b) = 0, U(T2, a) = 0, U(T2, b) = 2`. It is `ReflectivePolicy ∧ LocalUtility`
  (the latter for the degenerate reason that only two policies have mass, N−) but neither
  `IndependentPoints` nor `NoCrossBranch`; the one-step policy is `bb`; `exAnteValue bb = 1` and
  **`bb` is prior-optimal among the positive-mass policies** (`IsPriorOptimalOnSupport`); the
  pointwise-better policy `ab` has **mass `0`**, so `exAnteValue ab` is undefined (the junk `0`)
  and the program's `V(a, b) = 3/2` is `sepValue ab`, not `exAnteValue ab` — finding F-4. The
  U9(3) failure itself survives with full support and correlated points (`WitnessGap.lean`,
  `gapPrior`): what it needs is correlation, not null mass.
* **`corrPriorFull`** — the full-support variant with *independent* uniform points (same
  utilities): `IndependentPoints ∧ NoCrossBranch ∧ LocalUtility`, the one-step policy is `ab`,
  and `ab` is prior-optimal with value `3/2`: removing the correlation removes the failure.
* **`tnPrior`** — the Transparent-Newcomb-shaped prior: the point at `T1` moves the branch
  probability of `T1` (`9/10` vs `1/10`) while the other branch's value is constant. `Reflective`
  **fails**, `NoCrossBranch` holds, and the one-step and updateful rules separate at `T1` (one-step
  takes `true`, updateful takes `false`): the N− check that `Reflective` is a real hypothesis of
  T5, separately from `NoCrossBranch`.

All three are built by `handPrior`, whose faith is `faith_of_zeroOne` on the `{0,1}`-tables.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-- **A hand-built prior** over `{0,1}`-valued tables: the world's small truths are read off the
table that obtains, so faith holds for any base law (`faith_of_zeroOne`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def handPrior {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} (Ω₀ : Type)
    [Fintype Ω₀] (μ₀ : Ω₀ → ℚ) (hnn : ∀ ω, 0 ≤ μ₀ ω) (h1 : ∑ ω, μ₀ ω = 1)
    (state₀ : Ω₀ → ↥𝒟) (h01 : ∀ (T : ↥𝒟) (φ : ↥(𝒮.S m)), T.1 φ = 0 ∨ T.1 φ = 1)
    (pp₀ : Ω₀ → Policy 𝒟 A) (U₀ : Ω₀ → ℚ) : FiniteBLIPrior 𝒮 m 𝒟 A where
  Ω := Ω₀
  μ := μ₀
  μ_nonneg := hnn
  μ_sum_one := h1
  state := state₀
  pp := pp₀
  U := U₀
  small := fun ω φ => decide ((state₀ ω).1 φ = 1)
  faith := faith_of_zeroOne μ₀ state₀ h01

section HandPriorInstance

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} (Ω₀ : Type) [Fintype Ω₀]
  (μ₀ : Ω₀ → ℚ) (hnn : ∀ ω, 0 ≤ μ₀ ω) (h1 : ∑ ω, μ₀ ω = 1) (state₀ : Ω₀ → ↥𝒟)
  (h01 : ∀ (T : ↥𝒟) (φ : ↥(𝒮.S m)), T.1 φ = 0 ∨ T.1 φ = 1) (pp₀ : Ω₀ → Policy 𝒟 A) (U₀ : Ω₀ → ℚ)

/-- Masses of a hand-built prior are masses of its base law (swaps the `Fintype` instance so
that `simp` can expand the sum).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma handPrior_massOf (E : Ω₀ → Prop) [DecidablePred E] :
    massOf (handPrior Ω₀ μ₀ hnn h1 state₀ h01 pp₀ U₀).μ E = massOf μ₀ E := rfl

/-- Conditional expectations of a hand-built prior are those of its base law.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma handPrior_condExp (f : Ω₀ → ℚ) (E : Ω₀ → Prop) [DecidablePred E] :
    condExp (handPrior Ω₀ μ₀ hnn h1 state₀ h01 pp₀ U₀).μ f E = condExp μ₀ f E := rfl

end HandPriorInstance

/-- The junk value: a null policy has ex-ante value `0`.
Source: none: infrastructure (mandate T7: "the policy-level junk case")
Kind: L
Fidelity: n/a -/
lemma exAnteValue_eq_zero_of_null {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type}
    [DecidableEq A] (P : FiniteBLIPrior 𝒮 m 𝒟 A) (π : Policy 𝒟 A) (h : P.policyMass π = 0) :
    P.exAnteValue π = 0 := by
  unfold FiniteBLIPrior.exAnteValue condExp
  change _ / P.policyMass π = 0
  rw [h, div_zero]

/-! ## The two tables -/

/-- The two-table carrier `{Ask, Rec}`.
Source: [[bli-program]] §3.9(3)
Kind: D
Fidelity: exact -/
def twoTables : Finset (Table witIndex 1) := {mAsk, mRec}

/-- `Ask ∈ twoTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mAsk_mem_two : mAsk ∈ twoTables := by simp [twoTables]

/-- `Rec ∈ twoTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mRec_mem_two : mRec ∈ twoTables := by simp [twoTables]

/-- The first table `T1 = Ask`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev T1 : ↥twoTables := ⟨mAsk, mAsk_mem_two⟩

/-- The second table `T2 = Rec`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev T2 : ↥twoTables := ⟨mRec, mRec_mem_two⟩

/-- `T1 ≠ T2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma T1_ne_T2 : T1 ≠ T2 := fun h => mAsk_ne_mRec (congrArg Subtype.val h)

/-- `T2 ≠ T1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma T2_ne_T1 : T2 ≠ T1 := fun h => T1_ne_T2 h.symm

instance : Nonempty ↥twoTables := ⟨T1⟩

/-- Both tables are `{0,1}`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_zeroOne : ∀ (T : ↥twoTables) (φ : ↥(witIndex.S 1)), T.1 φ = 0 ∨ T.1 φ = 1 := by
  rintro ⟨T, hT⟩ φ
  simp only [twoTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl
  · simp only [mAsk]; split_ifs <;> simp
  · simp only [mRec]; split_ifs <;> simp

/-- The state coordinate `0 ↦ T1`, `1 ↦ T2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def twoState : Fin 2 → ↥twoTables
  | 0 => T1
  | 1 => T2

/-- `twoState 0 = T1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma twoState_zero : twoState 0 = T1 := rfl

/-- `twoState 1 = T2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma twoState_one : twoState 1 = T2 := rfl

/-- Every table of `twoTables` is `T1` or `T2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eq_T1_or_T2 (T : ↥twoTables) : T = T1 ∨ T = T2 := by
  rcases T with ⟨T, hT⟩
  simp only [twoTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The policy `ab`: `true` at `T1`, `false` at `T2`.
Source: [[bli-program]] §3.9(3)
Kind: D
Fidelity: exact -/
def abPol : Policy twoTables Bool := fun T => decide (T = T1)

/-- `abPol T1 = true`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma abPol_T1 : abPol T1 = true := by simp [abPol]

/-- `abPol T2 = false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma abPol_T2 : abPol T2 = false := by simp [abPol, Ne.symm mAsk_ne_mRec]

/-- No constant policy is `abPol`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma const_ne_abPol (c : Bool) : (fun _ : ↥twoTables => c) ≠ abPol := by
  intro h
  have h1 := congrFun h T1
  have h2 := congrFun h T2
  rw [abPol_T1] at h1
  rw [abPol_T2] at h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Two constant policies are equal iff their values are.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma const_eq_const_iff (c c' : Bool) :
    ((fun _ : ↥twoTables => c) = fun _ => c') ↔ c = c' := by
  constructor
  · intro h; exact congrFun h T1
  · intro h; rw [h]

/-- The universe of `↥twoTables` is `{T1, T2}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma univ_twoTables : (Finset.univ : Finset ↥twoTables) = {T1, T2} := by
  ext T
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact eq_T1_or_T2 T

/-! ## The correlated-points prior -/

/-- The utilities `U(T1, a) = 1, U(T1, b) = 0, U(T2, a) = 0, U(T2, b) = 2`, as a function of the
state and the common point value (`true = a`, `false = b`).
Source: [[bli-program]] §3.9(3)
Kind: D
Fidelity: exact -/
def corrU : Fin 2 → Bool → ℚ
  | 0 => fun c => if c then 1 else 0
  | 1 => fun c => if c then 0 else 2

/-- `corrU 0 c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma corrU_zero (c : Bool) : corrU 0 c = if c then 1 else 0 := rfl

/-- `corrU 1 c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma corrU_one (c : Bool) : corrU 1 c = if c then 0 else 2 := rfl

/-- **The correlated-points prior**: `Ω = Fin 2 × Bool` (state, the common point value), mass
`1/4` each, policy `fun _ => c` (both points equal), utility `corrU`.
Source: [[bli-program]] §3.9(3); mandate §3.5 (the gap witness)
Kind: D
Fidelity: exact -/
def corrPrior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool) (fun _ => 1 / 4) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ])
    (fun ω => twoState ω.1) two_zeroOne (fun ω _ => ω.2) (fun ω => corrU ω.1 ω.2)

namespace Corr

/-- Every state has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_eq (T : ↥twoTables) : corrPrior.stateMass T = 1 / 2 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;>
  · unfold FiniteBLIPrior.stateMass corrPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- A constant policy has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_const (c : Bool) : corrPrior.policyMass (fun _ => c) = 1 / 2 := by
  unfold FiniteBLIPrior.policyMass corrPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  cases c <;> norm_num [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- A non-constant policy is null.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_eq_zero (π : Policy twoTables Bool) (h : ∀ c, (fun _ : ↥twoTables => c) ≠ π) :
    corrPrior.policyMass π = 0 := by
  unfold FiniteBLIPrior.policyMass corrPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  simp [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, h]

/-- **`ab` is a null policy.**
Source: [[bli-program]] §3.9(3); mandate T7 ("`ab` … has `policyMass = 0`")
Kind: N−
Fidelity: exact -/
theorem policyMass_ab : corrPrior.policyMass abPol = 0 :=
  policyMass_eq_zero abPol const_ne_abPol

/-- A positive policy is constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma const_of_policyMass_pos (π : Policy twoTables Bool) (h : 0 < corrPrior.policyMass π) :
    ∃ c, (fun _ : ↥twoTables => c) = π := by
  by_contra hcon
  have : ∀ c, (fun _ : ↥twoTables => c) ≠ π := fun c hc => hcon ⟨c, hc⟩
  rw [policyMass_eq_zero π this] at h
  exact lt_irrefl _ h

/-- The cell of a constant policy has mass `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_const (T : ↥twoTables) (c : Bool) :
    corrPrior.cellMass T (fun _ => c) = 1 / 4 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases c <;>
  · unfold FiniteBLIPrior.cellMass corrPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- **`ReflectivePolicy` holds on the correlated-points prior.**
Source: mandate §3.5, T7
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem reflectivePolicy : corrPrior.ReflectivePolicy := by
  intro T π hπ
  obtain ⟨c, rfl⟩ := const_of_policyMass_pos π hπ
  rw [cellMass_const, policyMass_const, stateMass_eq]
  norm_num

/-- **`LocalUtility` holds on the correlated-points prior** (only constant policies have positive
cells, and two constant policies agreeing at a point are equal). N−: it holds for the degenerate
reason that only two policies have mass; the non-vacuous inhabitant of
`ReflectivePolicy ∧ LocalUtility ∧ ¬ NoCrossBranch` is `gapPrior` (`WitnessGap.lean`).
Source: mandate §3.5, T7
Kind: N−
Fidelity: exact (degenerate inhabitation, disclosed)
Hyps: (a) none -/
theorem localUtility : corrPrior.LocalUtility := by
  intro T π π' he hπ hπ'
  have hπpos : 0 < corrPrior.policyMass π :=
    lt_of_lt_of_le hπ (corrPrior.cellMass_le_policyMass T π)
  have hπ'pos : 0 < corrPrior.policyMass π' :=
    lt_of_lt_of_le hπ' (corrPrior.cellMass_le_policyMass T π')
  obtain ⟨c, rfl⟩ := const_of_policyMass_pos π hπpos
  obtain ⟨c', rfl⟩ := const_of_policyMass_pos π' hπ'pos
  have : c = c' := he
  rw [this]

/-- The point masses are `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_eq (T : ↥twoTables) (a : Bool) : corrPrior.ppMass T a = 1 / 2 := by
  unfold FiniteBLIPrior.ppMass corrPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  cases a <;> norm_num [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- **`IndependentPoints` fails**: `μ(pp · T1 = a ∧ pp · T2 = b) = 0 ≠ 1/4`.
Source: [[bli-program]] §3.9(3); mandate T7
Kind: N−
Fidelity: exact -/
theorem not_independentPoints : ¬ corrPrior.IndependentPoints := by
  intro h
  have := h T1 T2 true false T1_ne_T2
  rw [ppMass_eq, ppMass_eq] at this
  unfold FiniteBLIPrior.pairMass corrPrior at this
  rw [handPrior_massOf] at this
  simp only [handPrior] at this
  norm_num [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff] at this

/-- The joint cells `state = T2 ∧ pp · T1 = a` have mass `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_T2_T1 (a : Bool) : corrPrior.jointMass T2 T1 a = 1 / 4 := by
  unfold FiniteBLIPrior.jointMass corrPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  cases a <;> norm_num [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- `T2`'s expectation given the point at `T1`: `0` for `a`, `2` for `b`.
Source: [[bli-program]] §3.9(3)
Kind: L
Fidelity: n/a -/
lemma condEU_T2_T1 (a : Bool) : corrPrior.condEU T2 T1 a = if a then 0 else 2 := by
  unfold FiniteBLIPrior.condEU corrPrior
  rw [handPrior_condExp]
  simp only [handPrior]
  cases a <;> norm_num [condExp, massOf, integralOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- **`NoCrossBranch` fails**: the point at `T1` moves `T2`'s expectation from `0` to `2`.
Source: [[bli-program]] §3.9(3); mandate T7
Kind: N−
Fidelity: exact -/
theorem not_noCrossBranch : ¬ corrPrior.NoCrossBranch := by
  intro h
  have := h T1 T2 true false T2_ne_T1 (by rw [jointMass_T2_T1]; norm_num)
    (by rw [jointMass_T2_T1]; norm_num)
  rw [condEU_T2_T1, condEU_T2_T1] at this
  norm_num at this

/-- The one-step values: `EU T a = 1/2`, `EU T b = 1` at both tables.
Source: [[bli-program]] §3.9(3) (`EU(T1, a) = 1/2`, `EU(T1, b) = 1`)
Kind: L
Fidelity: n/a -/
lemma EU_eq (T : ↥twoTables) (a : Bool) : corrPrior.EU T a = if a then 1 / 2 else 1 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.EU corrPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- **The one-step policy is `bb`** (`false` at both tables), and `aa` is not one-step.
Source: [[bli-program]] §3.9(3) ("so it plays `b`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem oneStepPolicy_bb :
    corrPrior.IsOneStepPolicy (fun _ => false) ∧ ¬ corrPrior.IsOneStepChoice T1 true := by
  constructor
  · intro T b; rw [EU_eq, EU_eq]; cases b <;> norm_num
  · intro h; have := h false; rw [EU_eq, EU_eq] at this; norm_num at this

/-- The ex-ante values of the constant policies: `aa ↦ 1/2`, `bb ↦ 1`.
Source: [[bli-program]] §3.9(3) (`V(b, b) = 1`)
Kind: L
Fidelity: n/a -/
lemma exAnteValue_const (c : Bool) :
    corrPrior.exAnteValue (fun _ => c) = if c then 1 / 2 else 1 := by
  unfold FiniteBLIPrior.exAnteValue corrPrior
  rw [handPrior_condExp]
  simp only [handPrior]
  cases c <;> norm_num [condExp, massOf, integralOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- **`bb` is prior-optimal among the positive-mass policies** in the `𝔼[U | pp = π]` sense: the
constant policies score `1/2` and `1`; every other policy is null, its ex-ante value undefined,
so the guarded `IsPriorOptimalOnSupport` is the honest predicate here (the unguarded
`IsPriorOptimal` would hold only because the junk `0 ≤ 1`, and fails after shifting `U` by `−2`:
`WitnessGap.lean`, `Shift.corrShift_junk`).
Source: mandate T7; finding F-4
Kind: N+
Fidelity: exact (optimality among positive-mass policies)
Hyps: (a) none -/
theorem isPriorOptimal_bb : corrPrior.IsPriorOptimalOnSupport (fun _ => false) := by
  intro π' hπ'
  rw [exAnteValue_const]
  by_cases h : ∃ c, (fun _ : ↥twoTables => c) = π'
  · obtain ⟨c, rfl⟩ := h
    rw [exAnteValue_const]
    cases c <;> norm_num
  · have : ∀ c, (fun _ : ↥twoTables => c) ≠ π' := fun c hc => h ⟨c, hc⟩
    rw [policyMass_eq_zero π' this] at hπ'
    exact absurd hπ' (lt_irrefl _)

/-- The updateful values: `homeEU T1 a = 1, homeEU T1 b = 0, homeEU T2 a = 0, homeEU T2 b = 2`.
Source: [[bli-program]] §3.9(3)
Kind: L
Fidelity: n/a -/
lemma homeEU_eq (T : ↥twoTables) (a : Bool) :
    corrPrior.homeEU T a = if T = T1 then (if a then 1 else 0) else (if a then 0 else 2) := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU corrPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, const_eq_const_iff]

/-- **The separable values**: `sepValue ab = 3/2 > 1 = sepValue bb` — the program's `V(a, b) = 1.5`
is the separable formula, and on *this* prior the program's "strict preference for precommitment"
lives there, not in `exAnteValue` (where `ab` is null and `bb` is optimal among the positive
policies). On the full-support correlated prior `gapPrior` (`WitnessGap.lean`) it lives in
`exAnteValue` itself.
Source: [[bli-program]] §3.9(3) (`V(a, b) = 1.5 > 1 = V(b, b)`); finding F-4
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sepValue_ab_gt : corrPrior.sepValue abPol = 3 / 2 ∧
    corrPrior.sepValue (fun _ => false) = 1 ∧ corrPrior.exAnteValue abPol = 0 := by
  refine ⟨?_, ?_, exAnteValue_eq_zero_of_null _ _ policyMass_ab⟩
  · unfold FiniteBLIPrior.sepValue
    rw [univ_twoTables, Finset.sum_pair T1_ne_T2]
    simp only [stateMass_eq, homeEU_eq, abPol_T1, abPol_T2, if_true, T2_ne_T1, if_false]
    norm_num
  · unfold FiniteBLIPrior.sepValue
    rw [univ_twoTables, Finset.sum_pair T1_ne_T2]
    simp only [stateMass_eq, homeEU_eq, if_true, T2_ne_T1, if_false, Bool.false_eq_true]
    norm_num

/-- **`NDPOLICY` fails** on the correlated-points prior.
Source: mandate T7
Kind: N−
Fidelity: exact -/
theorem not_ndpolicy : ¬ corrPrior.NDPOLICY := fun h => by
  have := h abPol; rw [policyMass_ab] at this; exact lt_irrefl _ this

end Corr

/-! ## The full-support variant -/

/-- The base masses `1/2`, `1/2` of the full-support variant.
Source: mandate T7 ("put mass 1/4 on each of `aa, ab, ba, bb`")
Kind: D
Fidelity: exact -/
def halfMass : Fin 2 → ℚ := fun _ => 1 / 2

/-- The uniform point weights.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def twoHalf : ↥twoTables → Bool → ℚ := fun _ _ => 1 / 2

/-- The point weights sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoHalf_sum : ∀ T, ∑ a, twoHalf T a = 1 := by
  intro T; norm_num [twoHalf, Fintype.sum_bool]

/-- **The full-support variant**: independent uniform points, the same home-only utilities.
Source: mandate T7
Kind: D
Fidelity: exact -/
def corrDataFull : IndepData witIndex 1 twoTables Bool where
  Ω₀ := Fin 2
  μ₀ := halfMass
  μ₀_nonneg := fun _ => by norm_num [halfMass]
  μ₀_sum_one := by rw [Fin.sum_univ_two]; norm_num [halfMass]
  state₀ := twoState
  small₀ := fun s φ => decide ((twoState s).1 φ = 1)
  faith₀ := faith_of_zeroOne halfMass twoState two_zeroOne
  ν := prodLaw twoHalf
  ν_nonneg := prodLaw_nonneg (fun _ _ => by simp [twoHalf])
  ν_sum_one := sum_prodLaw twoHalf_sum
  U₀ := fun s π => corrU s (π (twoState s))

/-- The full-support prior.
Source: mandate T7
Kind: D
Fidelity: exact -/
def corrPriorFull : FiniteBLIPrior witIndex 1 twoTables Bool := corrDataFull.toPrior

namespace CorrFull

/-- The home-only shape.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma U₀_home : ∀ (s : Fin 2) (π : Policy twoTables Bool),
    corrDataFull.U₀ s π = corrU s (π (twoState s)) := fun _ _ => rfl

/-- `twoState` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma twoState_injective : Function.Injective twoState := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact absurd h T1_ne_T2
    | exact absurd h T2_ne_T1

/-- The conditional expectation on a base state is the value there.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_twoState (i : Fin 2) (f : Fin 2 → ℚ) :
    condExp halfMass f (fun s => twoState s = twoState i) = f i := by
  unfold condExp massOf integralOf
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · simp [halfMass]; ring
  all_goals first
    | (intro j _ hj; rw [if_neg (fun h => hj (twoState_injective h))])
    | (intro habs; exact absurd (Finset.mem_univ _) habs)

/-- **The full-support variant satisfies all the structural predicates and positivity.**
Source: mandate T7
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem structure_all :
    corrPriorFull.Reflective ∧ corrPriorFull.NoCrossBranch ∧ corrPriorFull.ReflectivePolicy ∧
      corrPriorFull.LocalUtility ∧ corrPriorFull.IndependentPoints ∧ corrPriorFull.NDPOL ∧
      corrPriorFull.NDHOME ∧ corrPriorFull.NDPOLICY := by
  have hpt : ∀ T a, 0 < massOf corrDataFull.ν (fun π => π T = a) := fun T a => by
    change 0 < massOf (prodLaw twoHalf) (fun π => π T = a)
    rw [IndepData.massOf_prodLaw_point twoHalf twoHalf_sum]; simp [twoHalf]
  have hs : ∀ T, 0 < massOf corrDataFull.μ₀ (fun s => corrDataFull.state₀ s = T) := by
    intro T
    rcases eq_T1_or_T2 T with rfl | rfl
    · change 0 < massOf halfMass (fun s => twoState s = twoState 0)
      unfold massOf; rw [Fin.sum_univ_two]
      simp [halfMass, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
    · change 0 < massOf halfMass (fun s => twoState s = twoState 1)
      unfold massOf; rw [Fin.sum_univ_two]
      simp [halfMass, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
  exact ⟨corrDataFull.reflective_toPrior,
    corrDataFull.noCrossBranch_home twoHalf twoHalf_sum rfl corrU U₀_home,
    corrDataFull.reflectivePolicy_toPrior,
    corrDataFull.localUtility_home twoHalf twoHalf_sum rfl corrU U₀_home,
    corrDataFull.independentPoints_toPrior_of_prodLaw twoHalf twoHalf_sum rfl,
    corrDataFull.ndpol_toPrior hpt, corrDataFull.ndhome_toPrior hs hpt,
    corrDataFull.ndpolicy_toPrior (fun π => prodLaw_pos (fun _ _ => by simp [twoHalf]) π)⟩

/-- The updateful values of the full-support variant are `corrU`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma homeEU_eq (i : Fin 2) (a : Bool) : corrPriorFull.homeEU (twoState i) a = corrU i a := by
  unfold corrPriorFull
  rw [corrDataFull.homeEU_home twoHalf twoHalf_sum rfl corrU U₀_home (twoState i) a
    (by simp [twoHalf])]
  exact condExp_twoState i (fun s => corrU s a)

/-- **In the full-support variant the one-step policy is `ab`, `ab` is prior-optimal, and its
value is `3/2`**: the tiling failure of the correlated prior disappears with independent points.
Source: mandate T7 ("check what survives"); [[bli-program]] §3.9 U9(2)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem oneStep_ab :
    corrPriorFull.IsOneStepPolicy abPol ∧ corrPriorFull.IsPriorOptimal abPol ∧
      corrPriorFull.exAnteValue abPol = 3 / 2 := by
  obtain ⟨hR, hN, hRp, hL, _, hpol, hhome, hpolicy⟩ := structure_all
  have hupd : corrPriorFull.IsUpdatefulPolicy abPol := by
    intro T b
    rcases eq_T1_or_T2 T with rfl | rfl
    · have h1 := homeEU_eq 0 b
      have h2 := homeEU_eq 0 true
      simp only [twoState_zero] at h1 h2
      rw [abPol_T1, h1, h2]; cases b <;> norm_num
    · have h1 := homeEU_eq 1 b
      have h2 := homeEU_eq 1 false
      simp only [twoState_one] at h1 h2
      rw [abPol_T2, h1, h2]; cases b <;> norm_num
  refine ⟨(corrPriorFull.oneStepPolicy_iff_updatefulPolicy hhome hR hN abPol).mpr hupd,
    corrPriorFull.priorOptimal_of_updatefulPolicy hpolicy hRp hL abPol hupd, ?_⟩
  rw [corrPriorFull.exAnteValue_eq_sepValue hRp hL abPol (hpolicy abPol)]
  unfold FiniteBLIPrior.sepValue
  rw [univ_twoTables, Finset.sum_pair T1_ne_T2]
  · have h1 := homeEU_eq 0 true
    have h2 := homeEU_eq 1 false
    simp only [twoState_zero, twoState_one] at h1 h2
    have hs : ∀ T, corrPriorFull.stateMass T = 1 / 2 := by
      intro T
      unfold corrPriorFull
      rw [corrDataFull.stateMass_toPrior]
      rcases eq_T1_or_T2 T with rfl | rfl
      · change massOf halfMass (fun s => twoState s = twoState 0) = 1 / 2
        unfold massOf; rw [Fin.sum_univ_two]
        simp [halfMass, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
      · change massOf halfMass (fun s => twoState s = twoState 1) = 1 / 2
        unfold massOf; rw [Fin.sum_univ_two]
        simp [halfMass, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
    rw [abPol_T1, abPol_T2, h1, h2, hs, hs]
    norm_num

end CorrFull

/-! ## The Transparent-Newcomb-shaped prior -/

/-- The masses of the Transparent-Newcomb-shaped prior: `(state, point at T1, point at T2)`;
the point at `T1` and the state are correlated (`9/10` vs `1/10`), the point at `T2` is an
independent fair coin.
Source: mandate §6 checklist ("`Reflective` checked false on a committed prior where the
corresponding conclusion fails")
Kind: D
Fidelity: exact -/
def tnMass : Fin 2 × Bool × Bool → ℚ := fun ω =>
  (if (ω.1 = 0) = (ω.2.1 = true) then 45 / 100 else 5 / 100) * (1 / 2)

/-- The policy points of the Transparent-Newcomb-shaped prior.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tnPP (ω : Fin 2 × Bool × Bool) : Policy twoTables Bool :=
  fun T => if T = T1 then ω.2.1 else ω.2.2

/-- The utility: at `T1`, `1000` for `true` and `1001` for `false`; `0` at `T2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def tnU : Fin 2 × Bool × Bool → ℚ := fun ω =>
  if ω.1 = 0 then (if ω.2.1 then 1000 else 1001) else 0

/-- **The Transparent-Newcomb-shaped prior.**
Source: mandate §6; [[bli-program]] §7 item 9
Kind: D
Fidelity: exact -/
def tnPrior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool × Bool) tnMass
    (fun ω => by unfold tnMass; split_ifs <;> norm_num)
    (by
      unfold tnMass
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]
      norm_num)
    (fun ω => twoState ω.1) two_zeroOne tnPP tnU

namespace TN

/-- `tnPP ω T1 = ω.2.1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tnPP_T1 (ω : Fin 2 × Bool × Bool) : tnPP ω T1 = ω.2.1 := by simp [tnPP]

/-- `tnPP ω T2 = ω.2.2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma tnPP_T2 (ω : Fin 2 × Bool × Bool) : tnPP ω T2 = ω.2.2 := by
  simp [tnPP, Ne.symm mAsk_ne_mRec]

/-- Every point has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_eq (T : ↥twoTables) (a : Bool) : tnPrior.ppMass T a = 1 / 2 := by
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.ppMass tnPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, tnMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, tnPP, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- `μ(state = T1 | pp · T1 = true) = 9/10`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma branchProb_T1_true : tnPrior.branchProb T1 T1 true = 9 / 10 := by
  unfold FiniteBLIPrior.branchProb
  rw [ppMass_eq]
  unfold FiniteBLIPrior.jointMass tnPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  norm_num [massOf, tnMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, tnPP, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- `μ(state = T1) = 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_T1 : tnPrior.stateMass T1 = 1 / 2 := by
  unfold FiniteBLIPrior.stateMass tnPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  norm_num [massOf, tnMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, tnPP, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- **`Reflective` fails**: the point at `T1` moves `T1`'s probability from `1/2` to `9/10`.
Source: mandate §6; [[bli-program]] §7 item 9
Kind: N−
Fidelity: exact -/
theorem not_reflective : ¬ tnPrior.Reflective := by
  intro h
  have := h T1 T1 true (by rw [ppMass_eq]; norm_num)
  rw [branchProb_T1_true, stateMass_T1] at this
  norm_num at this

/-- The one-step values at `T1`: `900` for `true`, `1001/10` for `false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EU_T1 (a : Bool) : tnPrior.EU T1 a = if a then 900 else 1001 / 10 := by
  cases a <;>
  · unfold FiniteBLIPrior.EU tnPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tnMass, tnU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, tnPP, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- The updateful values at `T1`: `1000` for `true`, `1001` for `false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma homeEU_T1 (a : Bool) : tnPrior.homeEU T1 a = if a then 1000 else 1001 := by
  cases a <;>
  · unfold FiniteBLIPrior.homeEU FiniteBLIPrior.condEU tnPrior
    rw [handPrior_condExp]
    simp only [handPrior]
    norm_num [condExp, massOf, integralOf, tnMass, tnU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, tnPP, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- **The two rules separate through branch re-weighting alone**: at `T1` the one-step choice is
`true` and the updateful choice is `false`.
Source: mandate §6 checklist; [[bli-program]] §7 item 9
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem separation :
    tnPrior.IsOneStepChoice T1 true ∧ ¬ tnPrior.IsUpdatefulChoice T1 true ∧
      tnPrior.IsUpdatefulChoice T1 false ∧ ¬ tnPrior.IsOneStepChoice T1 false := by
  refine ⟨fun b => ?_, fun h => ?_, fun b => ?_, fun h => ?_⟩
  · rw [EU_T1, EU_T1]; cases b <;> norm_num
  · have := h false; rw [homeEU_T1, homeEU_T1] at this; norm_num at this
  · rw [homeEU_T1, homeEU_T1]; cases b <;> norm_num
  · have := h true; rw [EU_T1, EU_T1] at this; norm_num at this

/-- The cross cells of the Transparent-Newcomb-shaped prior: `T2`'s expectation is `0` whatever
the point at `T1`; `T1`'s expectation given the (independent) point at `T2` is `10001/10` for
both values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condEU_cross (a : Bool) :
    tnPrior.condEU T2 T1 a = 0 ∧ tnPrior.condEU T1 T2 a = 10001 / 10 := by
  cases a <;>
  · constructor <;>
    · unfold FiniteBLIPrior.condEU tnPrior
      rw [handPrior_condExp]
      simp only [handPrior]
      norm_num [condExp, massOf, integralOf, tnMass, tnU, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, tnPP, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

/-- **`NoCrossBranch` holds** on the Transparent-Newcomb-shaped prior: the separation is purely
branch re-weighting.
Source: mandate §6 checklist
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem noCrossBranch : tnPrior.NoCrossBranch := by
  intro T T' a b hne _ _
  rcases eq_T1_or_T2 T with rfl | rfl <;> rcases eq_T1_or_T2 T' with rfl | rfl
  · exact absurd rfl hne
  · rw [(condEU_cross a).1, (condEU_cross b).1]
  · rw [(condEU_cross a).2, (condEU_cross b).2]
  · exact absurd rfl hne

/-- `NDPOL` and `NDHOME` hold on the Transparent-Newcomb-shaped prior.
Source: none: infrastructure
Kind: N+
Fidelity: exact -/
theorem ndpol_ndhome : tnPrior.NDPOL ∧ tnPrior.NDHOME := by
  constructor
  · intro T a; rw [ppMass_eq]; norm_num
  · intro T a
    rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
    · unfold FiniteBLIPrior.jointMass tnPrior
      rw [handPrior_massOf]
      simp only [handPrior]
      norm_num [massOf, tnMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, T1_ne_T2, T2_ne_T1, tnPP, Ne.symm mAsk_ne_mRec, mAsk_ne_mRec]

end TN

end Cleanroom.Bli.UdtBliCore
