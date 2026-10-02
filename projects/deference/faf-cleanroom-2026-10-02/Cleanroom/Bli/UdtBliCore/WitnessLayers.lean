import Cleanroom.Bli.UdtBliCore.WitnessCorr
import Cleanroom.Bli.UdtBliCore.Desiderata
import Cleanroom.Bli.UdtBliCore.Wirehead
import Cleanroom.Bli.UdtBliCore.WitnessXor
import Cleanroom.Bli.UdtBliCore.OfSkeleton

/-!
# `udt-bli-core` · WitnessLayers: faith without `FaithGivenPoints`, faith without `FaithGivenAct`,
the fair and unfair procedure layers, the entanglement instances behind finding F-11, and (repair
round 2) `CoordinationFree` checked false and the tent prior's entanglement

* **`fngPrior`** — one table `(p ↦ 1/2, q ↦ 0)`, a fair policy point, and `p` true exactly when the
  point is `true`: the `faith` field holds (`μ(p | state) = 1/2`) but `FaithGivenPoints` fails
  (`μ(p | state ∧ pp = true) = 1 ≠ 1/2`). Tells `udt-bli-sist` which hypothesis SIST's
  "branches believe …" premises need.
* **`wfPrior`** — the same table, `Ω = Bool` as the *current* action, `p` true iff the action is
  `true`, `U = [p]`: the `faith` field holds but `FaithGivenAct` fails, and the wireheading
  identity is **false** (`𝔼[U | act = true] = 1 ≠ 1/2`): the action-conditional faith
  `wirehead_identity` takes is a genuine strengthening of the source's constraint 2 (N−, F-17).
* **`layerPrior fairU` / `layerOf fairU`** — three procedures, `0` and `1` with the same effective
  behaviour (`const true`), `2` with `const false`; the environment pays by behaviour: **Policy
  Fairness holds** (N+). **`layerOf unfairU`** — the same procedures, the environment punishes
  procedure `1` ("written in C++"): **Policy Fairness fails** (N−).
* **`corrEntangled`** — the correlated-points prior is `CoordinationFree` (empty dependency maps)
  yet not `NoCrossBranch`: the independence-given-the-state clause of
  `noCrossBranch_of_coordinationFree` is needed.
* **`corrTNPrior` / `corrTNMandate`** — the mandate's single-map formulation
  (`EntangledMandate`, `MandateCoordinationFree`) does **not** give `Reflective` without
  `NDPOLICY`: two perfectly correlated policies `aa`, `bb` with branch probabilities `9/10` and
  `1/10` satisfy the clause vacuously and are not `Reflective`. (With `NDPOLICY` it does:
  `reflectivePolicy_of_mandateCoordinationFree` in `Desiderata.lean`.)
* **`Mugging.not_coordinationFree`** (repair r2) — no entanglement structure over the mugging
  prior is coordination-free, at either level: the checklist's negative for `CoordinationFree`
  (Desideratum 3's conclusion fails there).
* **`Xor.noCrossBranch_without_coordinationFree`** (repair r2) — the mandate's T10 gap in the
  direction it asked for: `NoCrossBranch` holds on the XOR prior (the dependence cancels in
  expectation) and no structure is coordination-free.
* **`Tent.no_entangled`** (repair r2) — the tent prior admits **no** `Entangled` structure: its
  utility is judged in the world, and `Entangled`'s utility clause is pointwise (finding F-18).
  **`Tent.tentEntangledExp` / `Tent.d3_on_tent`** — it carries a coordination-free
  `EntangledExp` (empty maps), and Desideratum 3 in expectation form holds there with a varying
  maximizer: the checklist's N+ for coordination-freeness on the tent skeleton, at the
  expectation level.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset FiniteBLIPrior

/-! ## Faith without `FaithGivenPoints` -/

/-- The one-table carrier `{(p ↦ 1/2, q ↦ 0)}` (`bli-finite`'s `Q₁`).
Source: mandate §3.4
Kind: D
Fidelity: exact -/
def oneTable : Finset (Table witIndex 1) := {Q₁}

/-- The table as an element of the carrier.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev TQ : ↥oneTable := ⟨Q₁, by simp [oneTable]⟩

/-- Every element of `oneTable` is `TQ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eq_TQ (T : ↥oneTable) : T = TQ := by
  rcases T with ⟨T, hT⟩
  simp only [oneTable, Finset.mem_singleton] at hT
  exact Subtype.ext hT

/-- **The faith-without-`FaithGivenPoints` prior**: `Ω = Bool` (the point), `p` true iff the point
is `true`, `q` false.
Source: mandate §3.4 ("a prior with `faith` but not `FaithGivenPoints`")
Kind: D
Fidelity: exact -/
def fngPrior : FiniteBLIPrior witIndex 1 oneTable Bool where
  Ω := Bool
  μ := fun _ => 1 / 2
  μ_nonneg := fun _ => by norm_num
  μ_sum_one := by norm_num [Fintype.sum_bool]
  state := fun _ => TQ
  pp := fun c _ => c
  U := fun _ => 0
  small := fun c φ => c && decide (φ.1 = pW)
  faith := by
    intro T φ
    rw [eq_TQ T]
    by_cases hφ : φ.1 = pW
    · norm_num [Fintype.sum_bool, ind, hφ, Q₁]
    · norm_num [Fintype.sum_bool, ind, hφ, Q₁]

/-- **`FaithGivenPoints` fails on `fngPrior`**: inside `pp · TQ = true` the frequency of `p` is `1`,
not the table's `1/2`; the `faith` field holds by construction.
Source: mandate §3.4 (the small N− for `udt-bli-sist`)
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem fng_not_faithGivenPoints : ¬ fngPrior.FaithGivenPoints := by
  intro h
  have hpos : 0 < fngPrior.jointMass TQ TQ true := by
    unfold FiniteBLIPrior.jointMass massOf fngPrior
    simp [Fintype.sum_bool]
  have := h TQ TQ true ⟨pW, pW_mem_S1⟩ hpos
  unfold integralOf FiniteBLIPrior.jointMass massOf fngPrior at this
  norm_num [Fintype.sum_bool, ind, Q₁] at this

/-! ## Faith without `FaithGivenAct`: the wireheading identity needs the action-conditional form -/

/-- **The `faith` field without `FaithGivenAct`**: `Ω = Bool` (the current action), one table
`Q₁ = (p ↦ 1/2, q ↦ 0)`, `p` true iff the action is `true`, `U = [p]`. The `faith` field holds
(`μ(p | state) = 1/2 = Q₁ p`); `FaithGivenAct` fails (`μ(p | state, act = true) = 1`).
Source: bli-soto-b-058 (constraint 2 versus the action-conditional form); audit r1 adversarial N1
Kind: D
Fidelity: n/a -/
def wfPrior : FiniteBLIPrior witIndex 1 oneTable Bool where
  Ω := Bool
  μ := fun _ => 1 / 2
  μ_nonneg := fun _ => by norm_num
  μ_sum_one := by norm_num [Fintype.sum_bool]
  state := fun _ => TQ
  pp := fun _ _ => true
  U := fun c => ind c
  small := fun c φ => c && decide (φ.1 = pW)
  faith := by
    intro T φ
    rw [eq_TQ T]
    by_cases hφ : φ.1 = pW
    · norm_num [Fintype.sum_bool, ind, hφ, Q₁]
    · norm_num [Fintype.sum_bool, ind, hφ, Q₁]

/-- The current-action coordinate of `wfPrior`: the world itself.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def wfAct (c : Bool) : Bool := c

/-- `U = [p]` is the small combination with coefficient `1` on `p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wf_smallCombination : wfPrior.SmallCombination Push.pCoef := by
  intro ω
  change ind ω = ∑ φ, Push.pCoef φ * ind (ω && decide (φ.1 = pW))
  rw [univ_S1, Finset.sum_pair subtype_p_ne_q]
  simp [Push.pCoef, pW_ne_qW.symm]

/-- The believed value of `U` at `Q₁` is `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wf_believedValue : FiniteBLIPrior.believedValue Push.pCoef TQ = 1 / 2 := by
  unfold FiniteBLIPrior.believedValue
  rw [univ_S1, Finset.sum_pair subtype_p_ne_q]
  simp [Push.pCoef, Q₁, pW_ne_qW.symm]

/-- **The wireheading identity fails under the `faith` field alone**: at `act = true` its two
sides are `1` and `1/2`, and `FaithGivenAct` fails. So `wirehead_identity`'s action-conditional
faith is a strengthening of the source's constraint 2 that the identity needs (finding F-17).
Source: bli-soto-b-058 ("Consequence 3 … with constraint 2 in force"); audit r1 adversarial N1
Kind: N−
Fidelity: exact (the identity's two sides computed on a one-world-per-action prior)
Hyps: (a) none -/
theorem wf_identity_fails :
    condExp wfPrior.μ wfPrior.U (fun ω => wfAct ω = true) = 1 ∧
      (∑ T, massOf wfPrior.μ (fun ω => wfAct ω = true ∧ wfPrior.state ω = T) /
        massOf wfPrior.μ (fun ω => wfAct ω = true) *
          FiniteBLIPrior.believedValue Push.pCoef T) = 1 / 2 ∧
      wfPrior.SmallCombination Push.pCoef ∧
      ¬ wfPrior.FaithGivenAct wfAct := by
  refine ⟨?_, ?_, wf_smallCombination, ?_⟩
  · unfold condExp integralOf massOf wfPrior wfAct
    norm_num [Fintype.sum_bool, ind]
  · rw [Fintype.sum_eq_single TQ (fun b hb => absurd (eq_TQ b) hb), wf_believedValue]
    unfold massOf wfPrior wfAct
    norm_num [Fintype.sum_bool]
  · intro h
    have hpos : 0 < massOf wfPrior.μ (fun ω => wfPrior.state ω = TQ ∧ wfAct ω = true) := by
      unfold massOf wfPrior wfAct; norm_num [Fintype.sum_bool]
    have := h TQ ⟨pW, pW_mem_S1⟩ true hpos
    unfold integralOf massOf wfPrior wfAct at this
    norm_num [Fintype.sum_bool, ind, Q₁] at this

/-! ## The procedure layers -/

/-- `(0 : Fin 3) ≠ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma fin3_01 : (0 : Fin 3) ≠ 1 := by decide
/-- `(0 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma fin3_02 : (0 : Fin 3) ≠ 2 := by decide
/-- `(1 : Fin 3) ≠ 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma fin3_12 : (1 : Fin 3) ≠ 2 := by decide

/-- The effective behaviour of the three procedures: `0, 1 ↦ const true`, `2 ↦ const false`.
Source: bli-paper-047 ("written in C++ rather than Python"); mandate §3.6
Kind: D
Fidelity: exact -/
def procEff : Fin 3 → Policy twoTables Bool
  | 0 => fun _ => true
  | 1 => fun _ => true
  | 2 => fun _ => false

/-- `procEff 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma procEff_zero : procEff 0 = fun _ => true := rfl
/-- `procEff 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma procEff_one : procEff 1 = fun _ => true := rfl
/-- `procEff 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma procEff_two : procEff 2 = fun _ => false := rfl

/-- The fair environment pays `1` for the behaviour `const true`, `0` for `const false`.
Source: mandate §3.6 (N+)
Kind: D
Fidelity: exact -/
def fairU : Fin 3 → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 0

/-- `fairU` values. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma fairU_zero : fairU 0 = 1 := rfl
/-- `fairU 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma fairU_one : fairU 1 = 1 := rfl
/-- `fairU 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma fairU_two : fairU 2 = 0 := rfl

/-- The unfair environment punishes procedure `1` though it behaves like procedure `0`.
Source: bli-paper-047 (punishing the "ritual of cognition"); mandate §3.6 (N−)
Kind: D
Fidelity: exact -/
def unfairU : Fin 3 → ℚ
  | 0 => 1
  | 1 => -1
  | 2 => 0

/-- `unfairU` values. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma unfairU_zero : unfairU 0 = 1 := rfl
/-- `unfairU 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma unfairU_one : unfairU 1 = -1 := rfl
/-- `unfairU 2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma unfairU_two : unfairU 2 = 0 := rfl

/-- A prior with a procedure coordinate: `Ω = Fin 2 × Fin 3` (state, procedure), mass `1/6`,
policy points the procedure's effective behaviour, utility `u` of the procedure.
Source: mandate §3.6
Kind: D
Fidelity: exact -/
def layerPrior (u : Fin 3 → ℚ) : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Fin 3) (fun _ => 1 / 6) (fun _ => by norm_num)
    (by norm_num [Finset.sum_const, Finset.card_univ])
    (fun ω => twoState ω.1) two_zeroOne (fun ω => procEff ω.2) (fun ω => u ω.2)

/-- The procedure layer over `layerPrior u`.
Source: mandate §3.6
Kind: D
Fidelity: exact -/
def layerOf (u : Fin 3 → ℚ) : ProcLayer (layerPrior u) where
  Proc := Fin 3
  proc := fun ω => ω.2
  eff := procEff
  pp_eff := fun _ => rfl

/-- The value of a procedure is its utility (the state is irrelevant).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma procEU_layerOf (u : Fin 3 → ℚ) (p : Fin 3) : (layerOf u).procEU p = u p := by
  unfold ProcLayer.procEU layerOf layerPrior
  rw [handPrior_condExp]
  simp only [handPrior]
  match p with
  | 0 =>
    simp only [condExp, massOf, integralOf, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three]
    norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm] <;> ring
  | 1 =>
    simp only [condExp, massOf, integralOf, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three]
    norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm] <;> ring
  | 2 =>
    simp only [condExp, massOf, integralOf, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three]
    norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm] <;> ring

/-- **Policy Fairness holds on the fair layer** (N+): procedures `0` and `1` have the same
behaviour and the same value `1`; procedure `2` behaves differently and scores `0`.
Source: bli-paper-047 (Policy Fairness); mandate §3.6
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem policyFair_fair : (layerPrior fairU).PolicyFair (layerOf fairU) ∧
    procEff 0 = procEff 1 ∧ procEff 2 ≠ procEff 0 := by
  refine ⟨?_, rfl, fun h => absurd (congrFun h T1) (by simp)⟩
  intro p q hpq _ _
  rw [procEU_layerOf, procEU_layerOf]
  have key : ∀ p : Fin 3, fairU p = if procEff p T1 then 1 else 0 := by
    intro p
    match p with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  have hpq' : procEff p = procEff q := hpq
  rw [key, key, hpq']

/-- **Policy Fairness fails on the unfair layer** (N−): procedures `0` and `1` behave identically
but score `1` and `−1`.
Source: bli-paper-047 ("unfair to punish agents for … being written in C++"); mandate §3.6
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem not_policyFair_unfair : ¬ (layerPrior unfairU).PolicyFair (layerOf unfairU) := by
  intro h
  have hpos : ∀ p : Fin 3, 0 < (layerOf unfairU).procMass p := by
    intro p
    unfold ProcLayer.procMass layerOf layerPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    match p with
    | 0 =>
      simp only [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
      norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm]
    | 1 =>
      simp only [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
      norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm]
    | 2 =>
      simp only [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
      norm_num [fin3_01, fin3_02, fin3_12, fin3_01.symm, fin3_02.symm, fin3_12.symm]
  have := h (0 : Fin 3) (1 : Fin 3) rfl (hpos 0) (hpos 1)
  rw [procEU_layerOf, procEU_layerOf] at this
  norm_num at this

/-! ## The entanglement instances behind F-11 -/

/-- **The correlated-points prior is coordination-free**: the utility on a branch reads only the
branch's own point, and the branch probabilities do not depend on the (positive) policy.
Source: mandate T10; finding F-11
Kind: N+
Fidelity: exact -/
def corrEntangled : corrPrior.Entangled where
  dep := fun _ => ∅
  depP := fun _ => ∅
  U_sound := by
    intro ω ω' hs hp
    have h1 : ω.1 = ω'.1 := CorrFull.twoState_injective hs
    have h2 : ω.2 = ω'.2 := hp _ (Finset.mem_insert_self _ _)
    change corrU ω.1 ω.2 = corrU ω'.1 ω'.2
    rw [h1, h2]
  mass_sound := by
    intro T π π' _
    by_cases hπ : ∃ c, (fun _ : ↥twoTables => c) = π
    · by_cases hπ' : ∃ c, (fun _ : ↥twoTables => c) = π'
      · obtain ⟨c, rfl⟩ := hπ
        obtain ⟨c', rfl⟩ := hπ'
        rw [Corr.cellMass_const, Corr.cellMass_const, Corr.policyMass_const,
          Corr.policyMass_const]
      · have hz : corrPrior.policyMass π' = 0 :=
          Corr.policyMass_eq_zero π' (fun c hc => hπ' ⟨c, hc⟩)
        have hz' : corrPrior.cellMass T π' = 0 :=
          le_antisymm (hz ▸ corrPrior.cellMass_le_policyMass T π') (corrPrior.cellMass_nonneg T π')
        rw [hz, hz', mul_zero, zero_mul]
    · have hz : corrPrior.policyMass π = 0 :=
        Corr.policyMass_eq_zero π (fun c hc => hπ ⟨c, hc⟩)
      have hz' : corrPrior.cellMass T π = 0 :=
        le_antisymm (hz ▸ corrPrior.cellMass_le_policyMass T π) (corrPrior.cellMass_nonneg T π)
      rw [hz, hz', mul_zero, zero_mul]

/-- **`CoordinationFree` does not give `NoCrossBranch` by itself**: the correlated-points prior is
coordination-free and not `NoCrossBranch` (its points are not independent given the state).
Source: mandate T10; finding F-11
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem coordinationFree_not_noCrossBranch :
    corrPrior.CoordinationFree corrEntangled ∧ ¬ corrPrior.NoCrossBranch :=
  ⟨fun _ => ⟨Finset.empty_subset _, rfl⟩, Corr.not_noCrossBranch⟩

/-- The masses of the correlated Transparent-Newcomb prior: policies `aa` (`true`) and `bb`
(`false`) only, with `μ(T1 | aa) = 9/10`, `μ(T1 | bb) = 1/10`.
Source: finding F-11
Kind: D
Fidelity: exact -/
def corrTNMass : Fin 2 × Bool → ℚ := fun ω =>
  if (ω.1 = 0) = (ω.2 = true) then 45 / 100 else 5 / 100

/-- **The correlated Transparent-Newcomb prior**: only two (correlated) policies have mass, and
they move the branch probabilities.
Source: finding F-11
Kind: D
Fidelity: exact -/
def corrTNPrior : FiniteBLIPrior witIndex 1 twoTables Bool :=
  handPrior (Fin 2 × Bool) corrTNMass
    (fun ω => by unfold corrTNMass; split_ifs <;> norm_num)
    (by unfold corrTNMass; simp [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool]; norm_num)
    (fun ω => twoState ω.1) two_zeroOne (fun ω _ => ω.2) (fun _ => 0)

namespace CorrTN

/-- Non-constant policies are null.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_eq_zero (π : Policy twoTables Bool) (h : ∀ c, (fun _ : ↥twoTables => c) ≠ π) :
    corrTNPrior.policyMass π = 0 := by
  unfold FiniteBLIPrior.policyMass corrTNPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  simp [massOf, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, h]

/-- The point masses are `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_T1 (a : Bool) : corrTNPrior.ppMass T1 a = 1 / 2 := by
  unfold FiniteBLIPrior.ppMass corrTNPrior
  rw [handPrior_massOf]
  simp only [handPrior]
  cases a <;> norm_num [massOf, corrTNMass, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fintype.sum_bool]

/-- `μ(state = T1 | pp · T1 = true) = 9/10 ≠ 1/2 = μ(state = T1)`.
Source: finding F-11
Kind: L
Fidelity: n/a -/
lemma branchProb_ne : corrTNPrior.branchProb T1 T1 true = 9 / 10 ∧
    corrTNPrior.stateMass T1 = 1 / 2 := by
  constructor
  · unfold FiniteBLIPrior.branchProb
    rw [ppMass_T1]
    unfold FiniteBLIPrior.jointMass corrTNPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, corrTNMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]
  · unfold FiniteBLIPrior.stateMass corrTNPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, corrTNMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      mAsk_ne_mRec, Ne.symm mAsk_ne_mRec]

/-- **`Reflective` fails** on the correlated Transparent-Newcomb prior.
Source: finding F-11
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem not_reflective : ¬ corrTNPrior.Reflective := by
  intro h
  have := h T1 T1 true (by rw [ppMass_T1]; norm_num)
  rw [branchProb_ne.1, branchProb_ne.2] at this
  norm_num at this

/-- **The mandate's single-map clause holds with `dep = ∅`** on the correlated Transparent-Newcomb
prior: the utility is constant, and two positive policies agreeing at any point are equal (only
the constant policies have mass), so the probability clause is vacuous.
Source: mandate T10 (its soundness clause); finding F-11
Kind: N−
Fidelity: exact -/
def corrTNMandate : corrTNPrior.EntangledMandate where
  dep := fun _ => ∅
  U_sound := fun _ _ _ _ => rfl
  mass_sound := by
    intro T π π' hagree
    by_cases hπ : ∃ c, (fun _ : ↥twoTables => c) = π
    · by_cases hπ' : ∃ c, (fun _ : ↥twoTables => c) = π'
      · obtain ⟨c, rfl⟩ := hπ
        obtain ⟨c', rfl⟩ := hπ'
        have : c = c' := hagree T (Finset.mem_insert_self _ _)
        rw [this]
      · have hz : corrTNPrior.policyMass π' = 0 :=
          policyMass_eq_zero π' (fun c hc => hπ' ⟨c, hc⟩)
        have hz' : corrTNPrior.cellMass T π' = 0 :=
          le_antisymm (hz ▸ corrTNPrior.cellMass_le_policyMass T π')
            (corrTNPrior.cellMass_nonneg T π')
        rw [hz, hz', mul_zero, zero_mul]
    · have hz : corrTNPrior.policyMass π = 0 :=
        policyMass_eq_zero π (fun c hc => hπ ⟨c, hc⟩)
      have hz' : corrTNPrior.cellMass T π = 0 :=
        le_antisymm (hz ▸ corrTNPrior.cellMass_le_policyMass T π)
          (corrTNPrior.cellMass_nonneg T π)
      rw [hz, hz', mul_zero, zero_mul]

/-- **The mandate's `CoordinationFree → Reflective` fails without `NDPOLICY`**: the correlated
Transparent-Newcomb prior is mandate-coordination-free with `dep = ∅` and not `Reflective`
(and not `NDPOLICY`).
Source: mandate T10; finding F-11
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem mandate_gap :
    corrTNPrior.MandateCoordinationFree corrTNMandate ∧ ¬ corrTNPrior.Reflective ∧
      ¬ corrTNPrior.NDPOLICY :=
  ⟨fun _ => Finset.empty_subset _, not_reflective, fun h => by
    have := h abPol
    rw [policyMass_eq_zero abPol const_ne_abPol] at this
    exact lt_irrefl _ this⟩

end CorrTN

/-! ## `CoordinationFree` checked false (repair round 2; audit r2 fidelity non-blocking 1,
adversarial N1) -/

namespace Mugging

/-- **No entanglement structure over the mugging prior is coordination-free**, at either level:
coordination-freeness gives `LocalUtility`, which the mugging prior lacks (`not_localUtility`).
The checklist's negative for `CoordinationFree` (mandate §6): on the mugging, Desideratum 3's
conclusion fails (one-step pays and updateful refuses at `Ask`, `Mugging.lean`).
Source: mandate §6 checklist; [[bli-program]] §7 item 9; audit r2 fidelity non-blocking 1
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem not_coordinationFree (r : Bool → ℚ) :
    (¬ ∃ E : (muggingPrior r).Entangled, (muggingPrior r).CoordinationFree E) ∧
      (¬ ∃ E : (muggingPrior r).EntangledExp, (muggingPrior r).CoordinationFreeExp E) :=
  ⟨fun ⟨E, hE⟩ => not_localUtility r ((muggingPrior r).localUtility_of_coordinationFree E hE),
   fun ⟨E, hE⟩ => not_localUtility r ((muggingPrior r).localUtility_of_coordinationFreeExp E hE)⟩

end Mugging

namespace Xor

/-- **`NoCrossBranch` without `CoordinationFree`** — the mandate's T10 N−, in the direction the
mandate asked for: on the XOR prior `NoCrossBranch` holds (the dependence of `T1`'s utility on
`T2`'s point cancels in expectation), yet no entanglement structure is coordination-free at either
level, because coordination-freeness gives `LocalUtility` and the XOR prior lacks it
(`not_localUtility`). `corrEntangled` is the other direction (coordination-free and not
`NoCrossBranch`).
Source: mandate T10 ("`NoCrossBranch` without `CoordinationFree` (a dependency that cancels —
N−)"); audit r2 adversarial N1
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem noCrossBranch_without_coordinationFree :
    xorPrior.NoCrossBranch ∧
      (∀ E : xorPrior.Entangled, ¬ xorPrior.CoordinationFree E) ∧
      (∀ E : xorPrior.EntangledExp, ¬ xorPrior.CoordinationFreeExp E) :=
  ⟨noCrossBranch,
   fun E hE => not_localUtility (xorPrior.localUtility_of_coordinationFree E hE),
   fun E hE => not_localUtility (xorPrior.localUtility_of_coordinationFreeExp E hE)⟩

end Xor

/-! ## The tent prior and entanglement (repair round 2; audit r2 adversarial N2; finding F-18) -/

namespace Tent

/-- **The tent prior admits no `Entangled` structure**: its utility is the bet at the home point
judged in the world (`tentU`), so two outcomes with the same trajectory and policy and different
worlds have different `U`, while `U_sound` with full agreement of the points forces them equal
(`U_eq_of_entangled`). So `Entangled`'s pointwise utility clause excludes every prior with world
randomness in `U`, and the mandate's checklist item "`CoordinationFree` inhabited on the tent
skeleton" cannot be met by `Entangled` (finding F-18); it is met by `EntangledExp`
(`tentEntangledExp`, `d3_on_tent`).
Source: audit r2 adversarial N2; mandate §6 checklist
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem no_entangled : ∀ _ : tentPrior.Entangled, False := by
  intro E
  have hne : Nonempty tentPrior.Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := tentPrior.μ_sum_one
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨⟨⟨σ, _⟩, π⟩⟩ := hne
  have hU : tentU (σ, fun _ => true) π = tentU (σ, fun _ => false) π :=
    tentPrior.U_eq_of_entangled E ((σ, fun _ => true), π) ((σ, fun _ => false), π) rfl rfl
  unfold tentU betOnP at hU
  split_ifs at hU <;> simp at hU

/-- **The tent prior carries a coordination-free `EntangledExp`** (empty maps), from its
`ReflectivePolicy ∧ LocalUtility` (`tentPrior_structure`).
Source: mandate §6 checklist ("inhabited (N+) on a prior built from `bli-finite`'s tent
skeleton"); audit r2 adversarial N2
Kind: D
Fidelity: exact -/
def tentEntangledExp : tentPrior.EntangledExp :=
  tentPrior.entangledExpOfPolicyLevel tentPrior_structure.2.2.1 tentPrior_structure.2.2.2.1

/-- **`CoordinationFreeExp` inhabited non-degenerately on the tent skeleton, and Desideratum 3
is a real statement there**: the structure is coordination-free in expectation, the tent prior
has independent points given the state and `NDPOL`, all nine tables are positive, so
`d3_finite_exp` applies at every table; and the maximizer it identifies varies
(`tentPrior_varying`): one-step takes `true` only at `Tone` and `false` only at `Tzero`.
Source: mandate §6 checklist; bli-soto-a-025 (Desideratum 3); audit r2 adversarial N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem d3_on_tent :
    tentPrior.CoordinationFreeExp tentEntangledExp ∧
      (∀ (T : ↥(grid witIndex witMesh.d 1)) (a : Bool),
        (tentPrior.IsOneStepChoice T a ↔ tentPrior.IsUpdatefulChoice T a)) ∧
      tentPrior.IsOneStepChoice Tone true ∧ ¬ tentPrior.IsOneStepChoice Tone false ∧
      tentPrior.IsOneStepChoice Tzero false ∧ ¬ tentPrior.IsOneStepChoice Tzero true := by
  obtain ⟨_, _, hR, hL, _, hI, _, hpol, _, _⟩ := tentPrior_structure
  have hcf : tentPrior.CoordinationFreeExp tentEntangledExp :=
    tentPrior.coordinationFreeExp_ofPolicyLevel hR hL
  have hd3 : ∀ T a, (tentPrior.IsOneStepChoice T a ↔ tentPrior.IsUpdatefulChoice T a) :=
    fun T a => tentPrior.d3_finite_exp tentEntangledExp hcf hI hpol T
      (by rw [stateMass_tentPrior]; norm_num) a
  obtain ⟨h1, h2, h3, h4, _⟩ := tentPrior_varying
  exact ⟨hcf, hd3, (hd3 _ _).mpr h1, fun h => h2 ((hd3 _ _).mp h),
    (hd3 _ _).mpr h3, fun h => h4 ((hd3 _ _).mp h)⟩

end Tent

end Cleanroom.Bli.UdtBliCore
