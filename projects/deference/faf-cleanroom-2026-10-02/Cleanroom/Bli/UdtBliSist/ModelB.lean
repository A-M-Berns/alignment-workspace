import Cleanroom.Bli.UdtBliSist.Inert
import Cleanroom.Bli.UdtBliSist.Freedom
import Cleanroom.Bli.UdtBliCore.WitnessCorr

/-!
# `udt-bli-sist` · ModelB: cross-branch utility versus branch re-weighing (T2 e)

bli-soto-a-2-011's two finite models of one mugging, over `udt-bli-core`'s `mugTables`
(`Ask = (1,0)`, `Rec = (0,1)` read as **`get`**, `Other = (0,0)` read as **`nothing`**).

* **Model A** (`modelA`, an `IndepData`): two branches `ask`/`get` of mass `1/2`, independent
  uniform points, the reward not part of the `get` observation: `U = −10·[pp·Ask = give]` at `ask`,
  `100·[pp·Ask = give]` at `get`. The policy point acts by **cross-branch utility**:
  `Reflective` holds (`reflective_A`), `NoCrossBranch` fails (`not_noCrossBranch_A`), and
  `EU Ask give = 45`, `EU Ask refuse = 0` (`EU_A`).
* **Model B** (`modelB`, hand-built over `Fin 3 × (Bool × Bool × Bool)` with `handPrior`): three
  branches `ask`/`get`/`nothing`, the reward observed (`U(get) = 100`, `U(nothing) = 0`, no policy
  point in the utility outside `ask`), and the joint law `μ(ask, ·) = 1/4`, `μ(get, give) = 1/4`,
  `μ(get, refuse) = 0`, `μ(nothing, give) = 0`, `μ(nothing, refuse) = 1/4`: the policy point acts
  by **re-weighing** — `μ(get | pp·Ask = give) = 1/2`, `μ(get | refuse) = 0`,
  `μ(nothing | give) = 0`, `μ(nothing | refuse) = 1/2` (`branchProb_B`), `Reflective` fails
  (`not_reflective_B`), and again `EU Ask give = 45`, `EU Ask refuse = 0` (`EU_B`).
* **The refinement lemma** (`refines`): Model B's `get ∪ nothing` is Model A's `get` branch
  refined by the observed reward — the cell masses add up (`μ_B(get ∧ a) + μ_B(nothing ∧ a) =
  μ_A(get ∧ a)` for both `a`), the branch values match where the cells are live
  (`𝔼_A[U | get, give] = 100 = 𝔼_B[U | get, give]`, `𝔼_A[U | get, refuse] = 0 =
  𝔼_B[U | nothing, refuse]`), and the two decompositions of `EU` agree (`EU_A = EU_B` at both
  actions). So "cross-branch utility" and "branch re-weighing" are two formulations of one
  problem, and `branchCut`'s weight clause (`Reflective`) is formulation-dependent.

`IndepData` cannot express Model B (`udt-bli-core` F-14), which is why it is hand-built.

Sources: bli-soto-a-2-011; bli-soto-b-2-011 (i); mandate T2(e); audit round 1 A2/B1.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging Finset
open Freedom

namespace ModelB

/-! ## Model A: two branches, cross-branch utility -/

/-- The masses of Model A: `ask` and `get` at `1/2`, no residual.
Source: bli-soto-a-2-011 (`P(ask) = P(get) = ½`)
Kind: D
Fidelity: exact -/
def mA : Fin 3 → ℚ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | 2 => 0

/-- The payoff of Model A as a function of the state and the `Ask` point: `−10·[give]` at `ask`,
`100·[give]` at `get`.
Source: bli-soto-a-2-011 (Model A's four conditional values)
Kind: D
Fidelity: exact -/
def fA : Fin 3 → Bool → ℚ := fun s b => if s = 0 then -10 * ind b else if s = 1 then 100 * ind b else 0

/-- **Model A's data**: base `Fin 3`, masses `mA`, independent uniform points, the payoff read at
`Ask`.
Source: bli-soto-a-2-011 (Model A)
Kind: D
Fidelity: exact -/
def dataA : IndepData witIndex 1 mugTables Bool where
  Ω₀ := Fin 3
  μ₀ := mA
  μ₀_nonneg := by intro s; fin_cases s <;> norm_num [mA]
  μ₀_sum_one := by rw [Fin.sum_univ_three]; norm_num [mA]
  state₀ := mugState
  small₀ := fun s φ => decide ((mugState s).1 φ = 1)
  faith₀ := faith_of_zeroOne _ _ mug_zeroOne
  ν := prodLaw mugHalf
  ν_nonneg := prodLaw_nonneg (fun _ _ => by simp [mugHalf])
  ν_sum_one := sum_prodLaw mugHalf_sum
  U₀ := fun s π => fA s (π askT)

/-- **Model A.**
Source: bli-soto-a-2-011 (Model A)
Kind: D
Fidelity: exact -/
def modelA : FiniteBLIPrior witIndex 1 mugTables Bool := dataA.toPrior

/-- Decidable equality of Model A's base.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instDecEqA : DecidableEq dataA.Ω₀ := inferInstanceAs (DecidableEq (Fin 3))

/-- Every point of Model A has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_point_A (T : ↥mugTables) (a : Bool) :
    massOf dataA.ν (fun π => π T = a) = 1 / 2 := by
  change massOf (prodLaw mugHalf) (fun π => π T = a) = 1 / 2
  rw [IndepData.massOf_prodLaw_point mugHalf mugHalf_sum]
  rfl

/-- **Model A's verdict**: `EU Ask give = 45`, `EU Ask refuse = 0`.
Source: bli-soto-a-2-011 (`E(U | give) = 45 > 0 = E(U | refuse)`)
Kind: C (the per-node class lemma with every state in the class; the refuse value by `EU_ref`)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_A : modelA.EU askT true = 45 ∧ modelA.EU askT false = 0 := by
  have hr : modelA.EU askT false = 0 := by
    unfold modelA
    rw [EU_ref dataA (fun _ => askT) fA (fun _ _ => rfl) askT false]
    have hpp : 0 < dataA.toPrior.ppMass askT false := by
      rw [IndepData.ppMass_toPrior, massOf_point_A]; norm_num
    simp only [condPoint_self dataA.toPrior askT _ false hpp]
    show ∑ s : Fin 3, mA s * ∑ b, (if b = false then (1 : ℚ) else 0) * fA s b = 0
    simp [fA, mA]
  have hd : modelA.EU askT true - modelA.EU askT false = 45 := by
    unfold modelA
    rw [classCut_ref_injective dataA mugState_injective
      (dataA.independentPoints_toPrior_of_prodLaw mugHalf mugHalf_sum rfl) (fun _ => askT) fA
      (fun _ _ => rfl) (univ : Finset (Fin 3)) askT (fun _ _ => rfl)
      (fun s hs => absurd (Finset.mem_univ s) hs) true false
      (by rw [massOf_point_A]; norm_num) (by rw [massOf_point_A]; norm_num)]
    show ∑ s : Fin 3, mA s * (fA s true - fA s false) = 45
    rw [Fin.sum_univ_three]
    norm_num [mA, fA]
  exact ⟨by linarith, hr⟩

/-- **Model A is `Reflective`**: the policy point moves no branch weight.
Source: bli-soto-a-2-011 ("the branch-cutting lemma (019) applies to Model A")
Kind: N+
Fidelity: exact -/
theorem reflective_A : modelA.Reflective := dataA.reflective_toPrior

/-- **Model A has cross-branch utility**: `𝔼[U | get, pp·Ask = give] = 100 ≠ 0 =
𝔼[U | get, pp·Ask = refuse]`, so `NoCrossBranch` fails.
Source: bli-soto-a-2-011 ("the policy point acts by cross-branch utility")
Kind: N−
Fidelity: exact -/
theorem not_noCrossBranch_A :
    modelA.condEU recT askT true = 100 ∧ modelA.condEU recT askT false = 0 ∧
      ¬ modelA.NoCrossBranch := by
  have hc : ∀ a, modelA.condEU recT askT a = fA 1 a := by
    intro a
    unfold modelA
    rw [condEU_ref_of_eq_single dataA mugState_injective (fun _ => askT) fA (fun _ _ => rfl)
      (1 : Fin 3) recT rfl askT rfl a (by rw [massOf_point_A]; norm_num)
      (by show mA 1 ≠ 0; norm_num [mA])]
  have hpos : ∀ a, 0 < modelA.jointMass recT askT a := by
    intro a
    unfold modelA
    rw [jointMass_toPrior_of_injective dataA mugState_injective (1 : Fin 3) recT rfl,
      massOf_point_A]
    show 0 < mA 1 * (1 / 2)
    norm_num [mA]
  refine ⟨by rw [hc]; simp [fA], by rw [hc]; simp [fA], fun h => ?_⟩
  have := h askT recT true false askT_ne_recT.symm (hpos true) (hpos false)
  rw [hc, hc] at this
  simp [fA] at this

/-! ## Model B: three branches, re-weighing -/

/-- The joint weights of the state and the `Ask` point: `ask` with either action at `1/4`,
`(get, give) = 1/4`, `(get, refuse) = 0`, `(nothing, give) = 0`, `(nothing, refuse) = 1/4`.
Source: bli-soto-a-2-011 (Model B's conditional branch probabilities, `P(ask) = ½`)
Kind: D
Fidelity: exact -/
def gB : Fin 3 → Bool → ℚ
  | 0, _ => 1 / 4
  | 1, true => 1 / 4
  | 1, false => 0
  | 2, true => 0
  | 2, false => 1 / 4

/-- Model B's outcome space: the state index and the three policy points.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev ΩB : Type := Fin 3 × (Bool × Bool × Bool)

/-- Model B's law: `gB` on `(state, Ask point)`, the other two points independent uniform.
Source: bli-soto-a-2-011 (Model B)
Kind: D
Fidelity: exact -/
def μB (ω : ΩB) : ℚ := gB ω.1 ω.2.1 / 4

/-- `μB ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma μB_nonneg (ω : ΩB) : 0 ≤ μB ω := by
  rcases ω with ⟨s, a, _, _⟩
  unfold μB
  fin_cases s <;> cases a <;> norm_num [gB]

/-- `∑ μB = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma μB_sum : ∑ ω, μB ω = 1 := by
  simp only [μB, Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, gB]
  norm_num

/-- Model B's utility: `−10·[give]` at `ask`, `100` at `get`, `0` at `nothing` — the reward is
observed, so no policy point enters outside `ask`.
Source: bli-soto-a-2-011 (`U(get) = 100`, `U(nothing) = 0`, `U(ask ∧ give) = −10`)
Kind: D
Fidelity: exact -/
def UB (ω : ΩB) : ℚ := if ω.1 = 0 then -10 * ind ω.2.1 else if ω.1 = 1 then 100 else 0

/-- **Model B**, hand-built (`IndepData` cannot re-weigh branches, `udt-bli-core` F-14).
Source: bli-soto-a-2-011 (Model B); mandate T2(e), §3.6
Kind: D
Fidelity: exact -/
def modelB : FiniteBLIPrior witIndex 1 mugTables Bool :=
  handPrior ΩB μB μB_nonneg μB_sum (fun ω => mugState ω.1) mug_zeroOne (fun ω => fmk ω.2) UB

/-- Both `Ask` points of Model B have mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_B (a : Bool) : modelB.ppMass askT a = 1 / 2 := by
  unfold FiniteBLIPrior.ppMass modelB
  rw [handPrior_massOf]
  simp only [handPrior]
  cases a <;> norm_num [massOf, μB, gB, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fintype.sum_bool, fmk_askT]

/-- The state masses of Model B: `ask` `1/2`, `get` `1/4`, `nothing` `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateMass_B : modelB.stateMass askT = 1 / 2 ∧ modelB.stateMass recT = 1 / 4 ∧
    modelB.stateMass otherT = 1 / 4 := by
  unfold FiniteBLIPrior.stateMass modelB
  simp only [handPrior]
  norm_num [massOf, μB, gB, Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool,
    mAsk_ne_mRec, mAsk_ne_mOther, mRec_ne_mOther, mAsk_ne_mRec.symm, mAsk_ne_mOther.symm,
    mRec_ne_mOther.symm]

/-- **The cell masses of Model B at the `Ask` point**: `(get, give) = 1/4`, `(get, refuse) = 0`,
`(nothing, give) = 0`, `(nothing, refuse) = 1/4`.
Source: bli-soto-a-2-011 (Model B's joint law)
Kind: L
Fidelity: exact -/
lemma jointMass_B : modelB.jointMass recT askT true = 1 / 4 ∧ modelB.jointMass recT askT false = 0 ∧
    modelB.jointMass otherT askT true = 0 ∧ modelB.jointMass otherT askT false = 1 / 4 := by
  unfold FiniteBLIPrior.jointMass modelB
  simp only [handPrior]
  norm_num [massOf, μB, gB, Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool,
    fmk_askT, mAsk_ne_mRec, mAsk_ne_mOther, mRec_ne_mOther, mAsk_ne_mRec.symm,
    mAsk_ne_mOther.symm, mRec_ne_mOther.symm]

/-- **The policy point re-weighs the branches**: `μ(get | pp·Ask = give) = 1/2`,
`μ(get | refuse) = 0`, `μ(nothing | give) = 0`, `μ(nothing | refuse) = 1/2`.
Source: bli-soto-a-2-011 ("the policy points shift probability between `get` and `nothing`")
Kind: P
Fidelity: exact -/
theorem branchProb_B : modelB.branchProb recT askT true = 1 / 2 ∧
    modelB.branchProb recT askT false = 0 ∧ modelB.branchProb otherT askT true = 0 ∧
    modelB.branchProb otherT askT false = 1 / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := jointMass_B
  unfold FiniteBLIPrior.branchProb
  rw [h1, h2, h3, h4, ppMass_B, ppMass_B]
  norm_num

/-- **Model B is not `Reflective`**: `μ(get | pp·Ask = give) = 1/2 ≠ 1/4 = μ(get)`.
Source: bli-soto-a-2-011 ("its branch clause fails in Model B")
Kind: N−
Fidelity: exact -/
theorem not_reflective_B : ¬ modelB.Reflective := by
  intro h
  have := h recT askT true (by rw [ppMass_B]; norm_num)
  rw [branchProb_B.1, stateMass_B.2.1] at this
  norm_num at this

/-- **Model B's verdict**: `EU Ask give = 45`, `EU Ask refuse = 0`.
Source: bli-soto-a-2-011 ("again `E(U | give) = 45`")
Kind: P
Fidelity: exact -/
theorem EU_B : modelB.EU askT true = 45 ∧ modelB.EU askT false = 0 := by
  unfold FiniteBLIPrior.EU modelB
  rw [handPrior_condExp, handPrior_condExp]
  simp only [handPrior]
  norm_num [condExp, integralOf, massOf, μB, gB, UB, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fintype.sum_bool, fmk_askT]
  all_goals decide

/-- **The branch values of Model B** where the cells are live: `𝔼[U | get, give] = 100`,
`𝔼[U | nothing, refuse] = 0` (the cells `(get, refuse)` and `(nothing, give)` are null, and their
`condEU` is the junk `0`).
Source: bli-soto-a-2-011
Kind: L
Fidelity: exact -/
lemma condEU_B : modelB.condEU recT askT true = 100 ∧ modelB.condEU otherT askT false = 0 := by
  unfold FiniteBLIPrior.condEU modelB
  rw [handPrior_condExp, handPrior_condExp]
  simp only [handPrior]
  norm_num [condExp, integralOf, massOf, μB, gB, UB, Fintype.sum_prod_type, Fin.sum_univ_three,
    Fintype.sum_bool, fmk_askT, mAsk_ne_mRec, mAsk_ne_mOther, mRec_ne_mOther, mAsk_ne_mRec.symm,
    mAsk_ne_mOther.symm, mRec_ne_mOther.symm]
  all_goals decide

/-! ## The refinement lemma -/

/-- **Model B refines Model A's `get` branch by the observed reward**: for both actions the cell
masses add up, `μ_B(get ∧ pp·Ask = a) + μ_B(nothing ∧ pp·Ask = a) = μ_A(get ∧ pp·Ask = a)`; the
live branch values match (`𝔼_A[U | get, give] = 100 = 𝔼_B[U | get, give]` and
`𝔼_A[U | get, refuse] = 0 = 𝔼_B[U | nothing, refuse]`); and the two decompositions of the
one-step value agree (`EU_A Ask a = EU_B Ask a` for both `a`). The same problem is cross-branch
utility in A (`Reflective`, not `NoCrossBranch`) and branch re-weighing in B (not `Reflective`).
Source: bli-soto-a-2-011 ("Model B is Model A with the `get` branch refined by the observed
reward, and the two decompositions of `E(U | A(ask) = a)` agree"); mandate T2(e)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem refines :
    (∀ a, modelB.jointMass recT askT a + modelB.jointMass otherT askT a =
      modelA.jointMass recT askT a) ∧
    (modelA.condEU recT askT true = modelB.condEU recT askT true ∧
      modelA.condEU recT askT false = modelB.condEU otherT askT false) ∧
    (∀ a, modelA.EU askT a = modelB.EU askT a) := by
  obtain ⟨b1, b2, b3, b4⟩ := jointMass_B
  obtain ⟨a1, a2, _⟩ := not_noCrossBranch_A
  obtain ⟨c1, c2⟩ := condEU_B
  obtain ⟨e1, e2⟩ := EU_A
  obtain ⟨f1, f2⟩ := EU_B
  have hA : ∀ a, modelA.jointMass recT askT a = 1 / 4 := by
    intro a
    unfold modelA
    rw [jointMass_toPrior_of_injective dataA mugState_injective (1 : Fin 3) recT rfl,
      massOf_point_A]
    show mA 1 * (1 / 2) = 1 / 4
    norm_num [mA]
  refine ⟨fun a => ?_, ⟨by rw [a1, c1], by rw [a2, c2]⟩, fun a => ?_⟩
  · cases a
    · rw [b2, b4, hA]; norm_num
    · rw [b1, b3, hA]; norm_num
  · cases a
    · rw [e2, f2]
    · rw [e1, f1]

end ModelB

end Cleanroom.Bli.UdtBliSist
