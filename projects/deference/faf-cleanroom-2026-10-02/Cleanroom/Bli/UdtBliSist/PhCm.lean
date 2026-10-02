import Cleanroom.Bli.UdtBliSist.FourTables
import Cleanroom.Bli.UdtBliSist.Inert
import Cleanroom.Bli.UdtBliSist.Crux

/-!
# `udt-bli-sist` · PhCm: problem-identity uncertainty — CM versus PH under inertness (T3 b)

bli-soto-a-2-015's finite model: the day-`m` tables split into a counterfactual-mugging class
`𝒟_CM = {CM_A, CM_R}` (the tables pricing the coin at `1`: `fAsk = (1,0)`, `fBoth = (1,1)`) and a
Parfit's-hitchhiker class `𝒟_PH = {PH_R, PH_A}` (`fRec = (0,1)`, `fOther = (0,0)`), masses `w`
(`μ(CM) = μ(PH) = 1/2` in the instance), independent uniform points, and the observed node
`Q̂ = CM_A`. **Utility**: `CM_A: −c·[pp·CM_A = pay]`, `CM_R: V·[pp·CM_A = pay]` (the mugging);
`PH_R: V'·[pp·X = pay]`, `PH_A: −c'·[pp·X = pay]` where **`X` is the table the PH tables read** —
`PH_A` (their own node) in the honest model, `CM_A` in the responsive variant.

* `classInert_cm`: with `X ≠ CM_A` the PH tables are inert at `Q̂` — **derived** from the
  construction by `classInert_of_ref`, not assumed;
* `verdict`: `EU Q̂ pay − EU Q̂ refuse = w(CM_R)·V − w(CM_A)·c` — the PH payoffs do not enter,
  although `μ(PH) = 1/2`: the argmax is the CM-optimal action (`isOneStepChoice_pay`);
* **N−** `verdict_responsive`, `not_classInert_responsive`: with `X = CM_A` the difference is
  `w(CM_R)·V − w(CM_A)·c + w(PH_R)·V' − w(PH_A)·c'`, inertness fails, and at the instance
  (`1/4` each, `(100, 10)`, `c' = 200`, `V' = 0`) the verdict flips to refuse
  (`instance_pay`, `instance_refuse`);
* **the crux where it bites** (`crux`): `𝒟_CM` is the `Σ`-class of `CM_A` for `Σ = {p}`
  (`sigmaClass_p`), so `oneStep_iff_twoStep` applies with its hypotheses derived — while the
  singleton `{CM_A}` is **not** inert (`CM_R` reads `pp·CM_A`), the updateful rule refuses and the
  one-step rule pays: one-step ≠ updateful, one-step = two-step. This is the witness the tent
  prior (`CruxTent`, inert through `NoCrossBranch`) cannot give.

Sources: bli-soto-a-2-015; mandate T3(b); audit round 1 A2/B1.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging Finset

namespace PhCm

/-- **The CM class** `{CM_A, CM_R} = {fAsk, fBoth}`: the tables asserting the node is a mugging.
Source: bli-soto-a-2-015 (`𝒟_CM`)
Kind: D
Fidelity: exact -/
def cmClass : Finset ↥fourTables := {fAsk, fBoth}

/-- The reference table: the CM states read the observed node `CM_A`; the PH states read `X`.
Source: bli-soto-a-2-015 ("the PH tables never observe `Q̂`" — `X ≠ CM_A`)
Kind: D
Fidelity: exact -/
def phRef (X : ↥fourTables) : Fin 4 → ↥fourTables
  | 0 => fAsk
  | 1 => fAsk
  | 2 => X
  | 3 => X

/-- The payoff: `−c·[pay]` at `CM_A`, `V·[pay]` at `CM_R`, `V'·[pay]` at `PH_R`, `−c'·[pay]` at
`PH_A`.
Source: bli-soto-a-2-015 ("the two problems have different optimal actions at the observed
node"); mandate T3(b)
Kind: D
Fidelity: exact (the PH payoffs are parameters; the instance takes `c' = 200`, `V' = 0`) -/
def phPay (c V c' V' : ℚ) : Fin 4 → Bool → ℚ
  | 0 => fun b => -c * ind b
  | 1 => fun b => V * ind b
  | 2 => fun b => V' * ind b
  | 3 => fun b => -c' * ind b

variable (w : Fin 4 → ℚ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) (X : ↥fourTables)
  (c V c' V' : ℚ)

/-- **The CM/PH data**: base `Fin 4` with masses `w`, the four tables, `0/1` faith, independent
uniform points, the payoff read at `phRef X`.
Source: bli-soto-a-2-015; mandate T3(b)
Kind: D
Fidelity: exact -/
def phData : IndepData witIndex 1 fourTables Bool where
  Ω₀ := Fin 4
  μ₀ := w
  μ₀_nonneg := hw
  μ₀_sum_one := hw1
  state₀ := fourState
  small₀ := fun s φ => decide ((fourState s).1 φ = 1)
  faith₀ := faith_of_zeroOne _ _ four_zeroOne
  ν := prodLaw fourHalf
  ν_nonneg := prodLaw_nonneg (fun _ _ => by simp [fourHalf])
  ν_sum_one := sum_prodLaw fourHalf_sum
  U₀ := fun s π => phPay c V c' V' s (π (phRef X s))

/-- **The CM/PH prior** (`X = fOther`: the PH tables read their own node; `X = fAsk`: the
responsive variant).
Source: bli-soto-a-2-015; mandate T3(b)
Kind: D
Fidelity: exact -/
def phPrior : FiniteBLIPrior witIndex 1 fourTables Bool := (phData w hw hw1 X c V c' V').toPrior

/-- The state coordinate of the data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma state₀_eq (s : Fin 4) : (phData w hw hw1 X c V c' V').state₀ s = fourState s := rfl

/-- Decidable equality of the base (it is `Fin 4`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instDecEqBase : DecidableEq (phData w hw hw1 X c V c' V').Ω₀ :=
  inferInstanceAs (DecidableEq (Fin 4))

/-- The points are independent.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma indep : (phData w hw hw1 X c V c' V').toPrior.IndependentPoints :=
  (phData w hw hw1 X c V c' V').independentPoints_toPrior_of_prodLaw fourHalf fourHalf_sum rfl

/-- Every point has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_point (T : ↥fourTables) (a : Bool) :
    massOf (phData w hw hw1 X c V c' V').ν (fun π => π T = a) = 1 / 2 := by
  change massOf (prodLaw fourHalf) (fun π => π T = a) = 1 / 2
  rw [IndepData.massOf_prodLaw_point fourHalf fourHalf_sum]
  rfl

/-- The utility has the reference shape.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma shaped : ∀ s π, (phData w hw hw1 X c V c' V').U₀ s π = phPay c V c' V' s (π (phRef X s)) :=
  fun _ _ => rfl

/-- **The PH tables are inert at the observed node** whenever they read a table other than it:
`ClassInert 𝒟_CM CM_A` — derived from the construction (independent points, the PH reference
`X ≠ CM_A`), not assumed.
Source: bli-soto-a-2-015 (the inertness hypothesis "made explicit"); mandate T3(b) ("derived
from the construction, not assumed")
Kind: N+ (the hypothesis of `classCut_of` inhabited on a two-class prior)
Fidelity: exact
Hyps: (a) `X ≠ CM_A` -/
theorem classInert_cm (hX : X ≠ fAsk) : ClassInert (phPrior w hw hw1 X c V c' V') cmClass fAsk := by
  unfold phPrior
  apply classInert_of_ref _ (indep w hw hw1 X c V c' V') (phRef X) (phPay c V c' V')
    (shaped w hw hw1 X c V c' V')
  show ∀ s : Fin 4, fourState s ∉ cmClass → phRef X s ≠ fAsk
  intro s hs
  fin_cases s
  · exact absurd (Finset.mem_insert_self _ _) hs
  · exact absurd (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hs
  · exact hX
  · exact hX

/-- The CM states read the observed node.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma phRef_eq : ∀ s ∈ ({0, 1} : Finset (Fin 4)), phRef X s = fAsk := by
  intro s hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl <;> rfl

/-- The PH states read `X`, not the observed node, when `X ≠ CM_A`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma phRef_ne (hX : X ≠ fAsk) : ∀ s ∉ ({0, 1} : Finset (Fin 4)), phRef X s ≠ fAsk := by
  intro s hs
  fin_cases s
  · exact absurd (Finset.mem_insert_self _ _) hs
  · exact absurd (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hs
  · exact hX
  · exact hX

/-- With `X = CM_A` every state reads the observed node.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma phRef_all : ∀ s ∈ (univ : Finset (Fin 4)), phRef fAsk s = fAsk := by
  intro s _
  fin_cases s <;> rfl

/-- **The verdict at the observed node is the CM verdict**: with the PH tables reading `X ≠ CM_A`,
`EU CM_A pay − EU CM_A refuse = w(CM_R)·V − w(CM_A)·c` — the PH payoffs and the PH mass do not
enter.
Source: bli-soto-a-2-015 ("the argmax is decided by the CM tables and is the CM-optimal action
although `P(CM) = ½`"); mandate T3(b)
Kind: C (`classCut_ref_injective` with `S = {CM_A, CM_R}`)
Fidelity: exact
Hyps: (a) `X ≠ CM_A`; does not use faith -/
theorem verdict (hX : X ≠ fAsk) :
    (phPrior w hw hw1 X c V c' V').EU fAsk true - (phPrior w hw hw1 X c V c' V').EU fAsk false =
      w 1 * V - w 0 * c := by
  unfold phPrior
  rw [classCut_ref_injective (phData w hw hw1 X c V c' V') fourState_injective
    (indep w hw hw1 X c V c' V') (phRef X) (phPay c V c' V') (shaped w hw hw1 X c V c' V')
    ({0, 1} : Finset (Fin 4)) fAsk (phRef_eq X) (phRef_ne X hX)
    true false (by rw [massOf_point]; norm_num) (by rw [massOf_point]; norm_num)]
  show ∑ s ∈ ({0, 1} : Finset (Fin 4)), w s * (phPay c V c' V' s true - phPay c V c' V' s false) =
    w 1 * V - w 0 * c
  rw [Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1)]
  simp only [phPay, ind_true, ind_false]
  ring

/-- **One-step UDT acts on the CM information it does not itself hold**: with `c·w(CM_A) <
V·w(CM_R)` and the PH tables inert, `pay` is the strict one-step choice at `CM_A`.
Source: bli-soto-a-2-015; mandate T3(b) ("conclusion `IsOneStepChoice Q̂ a` — by `classCut`")
Kind: C
Fidelity: exact
Hyps: (a) `X ≠ CM_A`, `c·w 0 < V·w 1`; does not use faith -/
theorem isOneStepChoice_pay (hX : X ≠ fAsk) (h : c * w 0 < V * w 1) :
    (phPrior w hw hw1 X c V c' V').IsOneStepChoice fAsk true ∧
      (phPrior w hw hw1 X c V c' V').EU fAsk false < (phPrior w hw hw1 X c V c' V').EU fAsk true := by
  have hd := verdict w hw hw1 X c V c' V' hX
  refine ⟨fun b => ?_, by linarith⟩
  cases b
  · linarith
  · exact le_rfl

/-! ## The N−: the PH tables made responsive to the observed node -/

/-- **The responsive variant's verdict**: with the PH tables reading `CM_A`,
`EU CM_A pay − EU CM_A refuse = w(CM_R)·V − w(CM_A)·c + w(PH_R)·V' − w(PH_A)·c'`.
Source: bli-soto-a-2-015 (the term reading "mixes both problems"); mandate T3(b) (N−)
Kind: C (`classCut_ref_injective` with every state in the class)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem verdict_responsive :
    (phPrior w hw hw1 fAsk c V c' V').EU fAsk true - (phPrior w hw hw1 fAsk c V c' V').EU fAsk false =
      w 1 * V - w 0 * c + w 2 * V' - w 3 * c' := by
  unfold phPrior
  rw [classCut_ref_injective (phData w hw hw1 fAsk c V c' V') fourState_injective
    (indep w hw hw1 fAsk c V c' V') (phRef fAsk) (phPay c V c' V') (shaped w hw hw1 fAsk c V c' V')
    (univ : Finset (Fin 4)) fAsk phRef_all (fun s hs => absurd (Finset.mem_univ s) hs)
    true false (by rw [massOf_point]; norm_num) (by rw [massOf_point]; norm_num)]
  show ∑ s : Fin 4, w s * (phPay c V c' V' s true - phPay c V c' V' s false) =
    w 1 * V - w 0 * c + w 2 * V' - w 3 * c'
  rw [Fin.sum_univ_four]
  simp only [phPay, ind_true, ind_false]
  ring

/-- **Inertness fails in the responsive variant**: `PH_A`'s value moves with the action at `CM_A`
(`−c'` versus `0`) when `PH_A` has mass and `c' ≠ 0`.
Source: bli-soto-a-2-015; mandate T3(b) ("N− the same prior with the PH tables made responsive
to `pp · Q̂` (inertness false, verdict flips)")
Kind: N−
Fidelity: exact
Hyps: (a) `0 < w 3`, `c' ≠ 0` -/
theorem not_classInert_responsive (hw3 : 0 < w 3) (hc' : c' ≠ 0) :
    ¬ ClassInert (phPrior w hw hw1 fAsk c V c' V') cmClass fAsk := by
  intro h
  have hmem : fourState 3 ∉ cmClass := by
    simp [cmClass, fAsk_ne_fOther.symm, fBoth_ne_fOther.symm]
  have hpos : ∀ a, 0 < (phPrior w hw hw1 fAsk c V c' V').jointMass (fourState 3) fAsk a := by
    intro a
    unfold phPrior
    rw [jointMass_toPrior_of_injective (phData w hw hw1 fAsk c V c' V') fourState_injective
      (3 : Fin 4) (fourState 3) rfl, massOf_point]
    exact mul_pos hw3 (by norm_num)
  have := h (fourState 3) hmem true false (hpos true) (hpos false)
  unfold phPrior at this
  rw [condEU_ref_of_eq_single (phData w hw hw1 fAsk c V c' V') fourState_injective (phRef fAsk)
      (phPay c V c' V') (shaped w hw hw1 fAsk c V c' V') (3 : Fin 4) (fourState 3) rfl fAsk rfl true
      (by rw [massOf_point]; norm_num) (ne_of_gt hw3),
    condEU_ref_of_eq_single (phData w hw hw1 fAsk c V c' V') fourState_injective (phRef fAsk)
      (phPay c V c' V') (shaped w hw hw1 fAsk c V c' V') (3 : Fin 4) (fourState 3) rfl fAsk rfl false
      (by rw [massOf_point]; norm_num) (ne_of_gt hw3)] at this
  simp only [phPay, ind_true, ind_false, mul_one, mul_zero, neg_eq_zero] at this
  exact hc' this

/-! ## The crux on the CM/PH prior -/

/-- **The CM class is the `Σ`-class of `CM_A` for `Σ = {p}`**: the tables agreeing with `CM_A`
on the coin are exactly `CM_A` and `CM_R`.
Source: mandate T5 (the `Σ`-class); bli-soto-a-2-015 (`𝒟_CM` "the tables asserting the node is
a counterfactual mugging")
Kind: L
Fidelity: exact -/
lemma sigmaClass_p : sigmaClass ({pS} : Finset ↥(witIndex.S 1)) fAsk = cmClass := by
  ext T
  rw [mem_sigmaClass_iff]
  unfold agreesOn
  simp only [Finset.mem_singleton, forall_eq]
  rcases eq_four T with rfl | rfl | rfl | rfl <;>
    simp [cmClass, mAsk, mBoth, mRec, mOther, mBoth_ne_mAsk, mAsk_ne_mRec.symm,
      mAsk_ne_mOther.symm, mBoth_ne_mAsk.symm, mBoth_ne_mRec.symm, mBoth_ne_mOther.symm]

/-- **The crux where it bites**: on the CM/PH prior with `X ≠ CM_A`, `0 < w(CM_A)`, `0 < c` and
`c·w(CM_A) < V·w(CM_R)`, the hypotheses of `oneStep_iff_twoStep` at `Σ = {p}`, `Q = CM_A` hold
(derived), so the one-step and two-step maximizer sets coincide; the singleton `{CM_A}` is **not**
inert; the updateful rule refuses and the one-step rule pays. So one-step ≠ updateful and
one-step = two-step on the same prior — "safe to update on `p`, not safe to update on the whole
table".
Source: mandate T5 (the trap: a class with `≥ 2` tables where the two-step conditional matters);
audit round 1 (fidelity item 5, adversarial item 1: the tent's inertness comes from
`NoCrossBranch`, which makes every class inert)
Kind: N+ (the hypotheses of `oneStep_iff_twoStep` inhabited where `branchCut`'s are not)
Fidelity: exact
Hyps: (a) `X ≠ CM_A`, `0 < w 0`, `0 < c`, `c·w 0 < V·w 1`; does not use faith -/
theorem crux (hX : X ≠ fAsk) (hw0 : 0 < w 0) (hc : 0 < c) (h : c * w 0 < V * w 1) :
    ReflectiveAt (phPrior w hw hw1 X c V c' V') fAsk ∧
      ClassInert (phPrior w hw hw1 X c V c' V') (sigmaClass ({pS} : Finset ↥(witIndex.S 1)) fAsk)
        fAsk ∧
      (∀ a, SigmaClassPos (phPrior w hw hw1 X c V c' V') ({pS} : Finset ↥(witIndex.S 1)) fAsk a) ∧
      (∀ a, (phPrior w hw hw1 X c V c' V').IsOneStepChoice fAsk a ↔
        IsTwoStepChoice (phPrior w hw hw1 X c V c' V') ({pS} : Finset ↥(witIndex.S 1)) fAsk a) ∧
      (phPrior w hw hw1 X c V c' V').IsOneStepChoice fAsk true ∧
      (phPrior w hw hw1 X c V c' V').IsUpdatefulChoice fAsk false ∧
      ¬ (phPrior w hw hw1 X c V c' V').IsUpdatefulChoice fAsk true ∧
      ¬ ClassInert (phPrior w hw hw1 X c V c' V') {fAsk} fAsk := by
  have hpt : ∀ a, 0 < massOf (phData w hw hw1 X c V c' V').ν (fun π => π fAsk = a) := by
    intro a; rw [massOf_point]; norm_num
  have hw1' : 0 < w 1 := by
    rcases lt_or_eq_of_le (hw 1) with h1 | h1
    · exact h1
    · rw [← h1] at h; nlinarith
  have hV : V ≠ 0 := by
    intro hV; rw [hV] at h; nlinarith
  have hR : ReflectiveAt (phPrior w hw hw1 X c V c' V') fAsk := by
    unfold phPrior
    exact reflectiveAt_of_reflective _ (phData w hw hw1 X c V c' V').reflective_toPrior fAsk
      (fun a => by rw [IndepData.ppMass_toPrior]; exact hpt a)
  have hI : ClassInert (phPrior w hw hw1 X c V c' V')
      (sigmaClass ({pS} : Finset ↥(witIndex.S 1)) fAsk) fAsk := by
    rw [sigmaClass_p]; exact classInert_cm w hw hw1 X c V c' V' hX
  have hjoint : ∀ a, 0 < (phPrior w hw hw1 X c V c' V').jointMass fAsk fAsk a := by
    intro a
    unfold phPrior
    rw [jointMass_toPrior_of_injective (phData w hw hw1 X c V c' V') fourState_injective
      (0 : Fin 4) fAsk rfl, massOf_point]
    exact mul_pos hw0 (by norm_num)
  have hpos : ∀ a, SigmaClassPos (phPrior w hw hw1 X c V c' V')
      ({pS} : Finset ↥(witIndex.S 1)) fAsk a := by
    intro a
    unfold SigmaClassPos
    rw [massOf_congr (phPrior w hw hw1 X c V c' V').μ (fun ω => by rw [← mem_sigmaClass_iff]),
      massOf_class, sigmaClass_p]
    exact lt_of_lt_of_le (hjoint a)
      (Finset.single_le_sum (fun T _ => (phPrior w hw hw1 X c V c' V').jointMass_nonneg T fAsk a)
        (Finset.mem_insert_self _ _))
  have hhome : ∀ a, (phPrior w hw hw1 X c V c' V').homeEU fAsk a = -c * ind a := by
    intro a
    unfold FiniteBLIPrior.homeEU phPrior
    rw [condEU_ref_of_eq_single (phData w hw hw1 X c V c' V') fourState_injective (phRef X)
      (phPay c V c' V') (shaped w hw hw1 X c V c' V') (0 : Fin 4) fAsk rfl fAsk rfl a (hpt a)
      (ne_of_gt hw0)]
    rfl
  have hsingle : ¬ ClassInert (phPrior w hw hw1 X c V c' V') {fAsk} fAsk := by
    intro hs
    have hmem : fBoth ∉ ({fAsk} : Finset ↥fourTables) := by
      simp only [Finset.mem_singleton]; exact fAsk_ne_fBoth.symm
    have hj : ∀ a, 0 < (phPrior w hw hw1 X c V c' V').jointMass fBoth fAsk a := by
      intro a
      unfold phPrior
      rw [jointMass_toPrior_of_injective (phData w hw hw1 X c V c' V') fourState_injective
        (1 : Fin 4) fBoth rfl, massOf_point]
      exact mul_pos hw1' (by norm_num)
    have := hs fBoth hmem true false (hj true) (hj false)
    unfold phPrior at this
    rw [condEU_ref_of_eq_single (phData w hw hw1 X c V c' V') fourState_injective (phRef X)
        (phPay c V c' V') (shaped w hw hw1 X c V c' V') (1 : Fin 4) fBoth rfl fAsk rfl true
        (hpt true) (ne_of_gt hw1'),
      condEU_ref_of_eq_single (phData w hw hw1 X c V c' V') fourState_injective (phRef X)
        (phPay c V c' V') (shaped w hw hw1 X c V c' V') (1 : Fin 4) fBoth rfl fAsk rfl false
        (hpt false) (ne_of_gt hw1')] at this
    simp only [phPay, ind_true, ind_false, mul_one, mul_zero] at this
    exact hV this
  refine ⟨hR, hI, hpos, fun a => oneStep_iff_twoStep _ _ _ hR hI hpos a,
    (isOneStepChoice_pay w hw hw1 X c V c' V' hX h).1, ?_, ?_, hsingle⟩
  · intro b
    rw [hhome, hhome]
    cases b
    · simp
    · simp; linarith
  · intro hu
    have := hu false
    rw [hhome, hhome] at this
    simp at this
    linarith

/-! ## The instance: `μ(CM) = μ(PH) = 1/2`, `(100, 10)`, PH cost `200` -/

/-- The masses `1/4` each.
Source: bli-soto-a-2-015 (`P(CM) = P(PH) = ½`)
Kind: D
Fidelity: exact -/
def wQ : Fin 4 → ℚ := fun _ => 1 / 4

/-- `wQ ≥ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wQ_nonneg : ∀ s, 0 ≤ wQ s := by intro s; norm_num [wQ]

/-- `∑ wQ = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wQ_sum : ∑ s, wQ s = 1 := by rw [Fin.sum_univ_four]; norm_num [wQ]

/-- **The instance pays** when the PH tables read their own node: the difference is `45/2`.
Source: bli-soto-a-2-015; mandate T3(b) (N+)
Kind: N+
Fidelity: exact -/
theorem instance_pay :
    (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0).EU fAsk true -
        (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0).EU fAsk false = 45 / 2 ∧
      (phPrior wQ wQ_nonneg wQ_sum fOther 10 100 200 0).IsOneStepChoice fAsk true := by
  have hd := verdict wQ wQ_nonneg wQ_sum fOther 10 100 200 0 fAsk_ne_fOther.symm
  refine ⟨by rw [hd]; norm_num [wQ], ?_⟩
  exact (isOneStepChoice_pay wQ wQ_nonneg wQ_sum fOther 10 100 200 0 fAsk_ne_fOther.symm
    (by norm_num [wQ])).1

/-- **The instance refuses** when the PH tables respond to the observed node: the difference is
`−55/2`, inertness fails, and `pay` is not a one-step choice.
Source: bli-soto-a-2-015; mandate T3(b) (N−: "inertness false, verdict flips")
Kind: N−
Fidelity: exact -/
theorem instance_refuse :
    (phPrior wQ wQ_nonneg wQ_sum fAsk 10 100 200 0).EU fAsk true -
        (phPrior wQ wQ_nonneg wQ_sum fAsk 10 100 200 0).EU fAsk false = -(55 / 2) ∧
      ¬ ClassInert (phPrior wQ wQ_nonneg wQ_sum fAsk 10 100 200 0) cmClass fAsk ∧
      (phPrior wQ wQ_nonneg wQ_sum fAsk 10 100 200 0).IsOneStepChoice fAsk false ∧
      ¬ (phPrior wQ wQ_nonneg wQ_sum fAsk 10 100 200 0).IsOneStepChoice fAsk true := by
  have hd := verdict_responsive wQ wQ_nonneg wQ_sum 10 100 200 0
  have hd' : (phPrior wQ wQ_nonneg wQ_sum fAsk 10 100 200 0).EU fAsk true -
      (phPrior wQ wQ_nonneg wQ_sum fAsk 10 100 200 0).EU fAsk false = -(55 / 2) := by
    rw [hd]; norm_num [wQ]
  refine ⟨hd', not_classInert_responsive wQ wQ_nonneg wQ_sum 10 100 200 0 (by norm_num [wQ])
    (by norm_num), fun b => ?_, fun h => ?_⟩
  · cases b
    · exact le_rfl
    · linarith
  · have := h false
    linarith

end PhCm

end Cleanroom.Bli.UdtBliSist
