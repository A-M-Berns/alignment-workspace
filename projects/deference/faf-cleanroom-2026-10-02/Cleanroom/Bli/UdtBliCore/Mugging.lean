import Cleanroom.Bli.UdtBliCore.ProductUtil
import Cleanroom.Bli.BliFinite.Witness
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# `udt-bli-core` · Mugging: the counterfactual-mugging prior (T3, definition of record)

The one mugging object of the run (`muggingPrior r`), parametrized by the residual branch's
utility `r : Bool → ℚ` so that `udt-bli-sist` can vary it. Numbers from bli-slides-034 /
[[bli-program]] §3.9 U5: three tables `Ask`, `Rec`, `Other` of masses `49/100`, `49/100`,
`2/100`; actions `Bool` with `true = pay`, `false = refuse`; utility `−10·[pp·Ask = pay]` on
`Ask`, `100·[pp·Ask = pay]` on `Rec`, `r (pp·Ask)` on `Other`; policy points independent of the
state and of each other, uniform `1/2` each (`IndepData` with the product law). Tables over
`witIndex` day 1 with `Ask = (1, 0)`, `Rec = (0, 1)`, `Other = (0, 0)`, so faith is inhabited by
the obvious `small`.

Witness facts proved here (for `|r| ≤ 10`): the one-step rule at `Ask` **pays**
(`EU Ask pay = 441/10 + (2/100) r pay > (2/100) r refuse = EU Ask refuse`); the updateful rule at
`Ask` **refuses** (`homeEU Ask pay = −10 < 0 = homeEU Ask refuse`); `NoCrossBranch` **fails**
(the `Rec` cell moves by `100` with `pp·Ask`) while `Reflective`, `ReflectivePolicy` and
`IndependentPoints` **hold** (so the separation is purely cross-branch utility);
`LocalUtility` **fails**; the constant pay policy is prior-optimal and beats every updateful
policy by `441/10 + (2/100)(r pay − r refuse) > 0`; `NDPOL`, `NDHOME`, `NDPOLICY` hold. These are
the N− rows of T5/T6 (the hypotheses are false exactly where the conclusions fail). The general
SIST verdict is `udt-bli-sist`'s and is not stated here.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

/-! ## Faith for 0/1 tables -/

/-- **Faith for hand-built priors whose small truths are read off a 0/1 table**: if every table
in `𝒟` is `{0,1}`-valued and the world's small truths are `decide (T φ = 1)` for the table `T`
that obtains, the faith identity holds for any base law.
Source: none: infrastructure (mandate T3: "faith is inhabited by the obvious `small`")
Kind: L
Fidelity: n/a -/
lemma faith_of_zeroOne {Ω₀ : Type} [Fintype Ω₀] (μ₀ : Ω₀ → ℚ) {𝒮 : SmallIndex} {m : ℕ}
    {𝒟 : Finset (Table 𝒮 m)} (state₀ : Ω₀ → ↥𝒟)
    (h01 : ∀ (T : ↥𝒟) (φ : ↥(𝒮.S m)), T.1 φ = 0 ∨ T.1 φ = 1) (T : ↥𝒟) (φ : ↥(𝒮.S m)) :
    integralOf μ₀ (fun ω => ind (decide ((state₀ ω).1 φ = 1))) (fun ω => state₀ ω = T) =
      T.1 φ * massOf μ₀ (fun ω => state₀ ω = T) := by
  rw [← integralOf_const]
  apply integralOf_congr_fun
  intro ω hω
  rw [hω]
  rcases h01 T φ with h | h
  · rw [h]; simp [ind]
  · rw [h]; simp [ind]

/-! ## The three tables -/

/-- The `Ask` table: `p ↦ 1`, `q ↦ 0`.
Source: bli-slides-034; mandate §3.7
Kind: D
Fidelity: exact -/
def mAsk : Table witIndex 1 := fun φ => if φ.1 = pW then 1 else 0

/-- The `Rec` table: `p ↦ 0`, `q ↦ 1`.
Source: bli-slides-034; mandate §3.7
Kind: D
Fidelity: exact -/
def mRec : Table witIndex 1 := fun φ => if φ.1 = pW then 0 else 1

/-- The residual `Other` table: `p ↦ 0`, `q ↦ 0`.
Source: bli-slides-034 (the 2% residual); mandate §3.7
Kind: D
Fidelity: exact -/
def mOther : Table witIndex 1 := fun _ => 0

/-- `Ask ≠ Rec`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mAsk_ne_mRec : mAsk ≠ mRec := fun h => by
  have := congrFun h ⟨pW, pW_mem_S1⟩
  simp [mAsk, mRec] at this

/-- `Ask ≠ Other`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mAsk_ne_mOther : mAsk ≠ mOther := fun h => by
  have := congrFun h ⟨pW, pW_mem_S1⟩
  simp [mAsk, mOther] at this

/-- `Rec ≠ Other`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mRec_ne_mOther : mRec ≠ mOther := fun h => by
  have := congrFun h ⟨qW, qW_mem_S1⟩
  simp [mRec, mOther, pW_ne_qW.symm] at this

/-- The three tables of the mugging.
Source: bli-slides-034; mandate §3.7
Kind: D
Fidelity: exact -/
def mugTables : Finset (Table witIndex 1) := {mAsk, mRec, mOther}

/-- `Ask ∈ mugTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mAsk_mem : mAsk ∈ mugTables := by simp [mugTables]

/-- `Rec ∈ mugTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mRec_mem : mRec ∈ mugTables := by simp [mugTables]

/-- `Other ∈ mugTables`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mOther_mem : mOther ∈ mugTables := by simp [mugTables]

/-- Every mugging table is `{0,1}`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mug_zeroOne : ∀ (T : ↥mugTables) (φ : ↥(witIndex.S 1)), T.1 φ = 0 ∨ T.1 φ = 1 := by
  rintro ⟨T, hT⟩ φ
  simp only [mugTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  · simp only [mAsk]; split_ifs <;> simp
  · simp only [mRec]; split_ifs <;> simp
  · simp [mOther]

/-- The `Ask` state.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev askT : ↥mugTables := ⟨mAsk, mAsk_mem⟩

/-- The `Rec` state.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev recT : ↥mugTables := ⟨mRec, mRec_mem⟩

/-- The `Other` state.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev otherT : ↥mugTables := ⟨mOther, mOther_mem⟩

/-- `askT ≠ recT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askT_ne_recT : askT ≠ recT := fun h => mAsk_ne_mRec (congrArg Subtype.val h)

/-- `askT ≠ otherT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askT_ne_otherT : askT ≠ otherT := fun h => mAsk_ne_mOther (congrArg Subtype.val h)

/-- `recT ≠ otherT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma recT_ne_otherT : recT ≠ otherT := fun h => mRec_ne_mOther (congrArg Subtype.val h)

/-! ## The base: three states, the masses, the utility -/

/-- The state coordinate of the base: `0 ↦ Ask`, `1 ↦ Rec`, `2 ↦ Other`.
Source: mandate §3.7
Kind: D
Fidelity: exact -/
def mugState : Fin 3 → ↥mugTables
  | 0 => askT
  | 1 => recT
  | 2 => otherT

/-- The branch masses `49/100`, `49/100`, `2/100`.
Source: bli-slides-034 ("49% each", the 2% residual); [[bli-program]] §3.9 U5
Kind: D
Fidelity: exact -/
def mugMass : Fin 3 → ℚ
  | 0 => 49 / 100
  | 1 => 49 / 100
  | 2 => 2 / 100

/-- The utility as a function of the state and of the `Ask` point: `−10·[pay]` at `Ask`,
`100·[pay]` at `Rec`, `r` at `Other`.
Source: bli-slides-034 (the payoff table); mandate §3.7
Kind: D
Fidelity: exact (with the residual parametrized by `r`) -/
def mugU (r : Bool → ℚ) : Fin 3 → Bool → ℚ
  | 0 => fun a => if a then -10 else 0
  | 1 => fun a => if a then 100 else 0
  | 2 => r

/-- `mugState 0 = askT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugState_zero : mugState 0 = askT := rfl

/-- `mugState 1 = recT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugState_one : mugState 1 = recT := rfl

/-- `mugState 2 = otherT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugState_two : mugState 2 = otherT := rfl

/-- `mugMass 0 = 49/100`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugMass_zero : mugMass 0 = 49 / 100 := rfl

/-- `mugMass 1 = 49/100`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugMass_one : mugMass 1 = 49 / 100 := rfl

/-- `mugMass 2 = 2/100`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugMass_two : mugMass 2 = 2 / 100 := rfl

/-- `mugU r 0 a = −10·[a]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugU_zero (r : Bool → ℚ) (a : Bool) : mugU r 0 a = if a then -10 else 0 := rfl

/-- `mugU r 1 a = 100·[a]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugU_one (r : Bool → ℚ) (a : Bool) : mugU r 1 a = if a then 100 else 0 := rfl

/-- `mugU r 2 = r`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma mugU_two (r : Bool → ℚ) (a : Bool) : mugU r 2 a = r a := rfl

/-- The uniform coordinate weights `1/2` on each point.
Source: mandate §3.7 ("independent points, uniform 1/2 each")
Kind: D
Fidelity: exact -/
def mugHalf : ↥mugTables → Bool → ℚ := fun _ _ => 1 / 2

/-- The coordinate weights sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mugHalf_sum : ∀ T, ∑ a, mugHalf T a = 1 := by
  intro T; norm_num [mugHalf, Fintype.sum_bool]

/-- `mugState` is injective (the three tables are distinct).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mugState_injective : Function.Injective mugState := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact absurd h askT_ne_recT
    | exact absurd h askT_ne_otherT
    | exact absurd h recT_ne_otherT
    | exact absurd h.symm askT_ne_recT
    | exact absurd h.symm askT_ne_otherT
    | exact absurd h.symm recT_ne_otherT

/-- The mass of a base state is its `mugMass`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_mugState (i : Fin 3) :
    massOf mugMass (fun s => mugState s = mugState i) = mugMass i := by
  unfold massOf
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg (fun h => hj (mugState_injective h))]
  · intro habs; exact absurd (Finset.mem_univ _) habs

/-- The conditional expectation of any `f` on a base state is `f` at that state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_mugState (i : Fin 3) (f : Fin 3 → ℚ) :
    condExp mugMass f (fun s => mugState s = mugState i) = f i := by
  unfold condExp
  rw [massOf_mugState]
  have : integralOf mugMass f (fun s => mugState s = mugState i) = mugMass i * f i := by
    unfold integralOf
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg (fun h => hj (mugState_injective h))]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  rw [this]
  have hpos : 0 < mugMass i := by fin_cases i <;> norm_num [mugMass]
  rw [mul_div_cancel_left₀ _ (ne_of_gt hpos)]

/-- **The mugging data** (independent uniform points over the three-state base).
Source: bli-slides-034; [[bli-program]] §3.9 U5; mandate §3.7
Kind: D
Fidelity: exact (finite; `r` parametrizes the residual branch) -/
def muggingData (r : Bool → ℚ) : IndepData witIndex 1 mugTables Bool where
  Ω₀ := Fin 3
  μ₀ := mugMass
  μ₀_nonneg := by intro s; fin_cases s <;> norm_num [mugMass]
  μ₀_sum_one := by rw [Fin.sum_univ_three]; norm_num [mugMass]
  state₀ := mugState
  small₀ := fun s φ => decide ((mugState s).1 φ = 1)
  faith₀ := faith_of_zeroOne mugMass mugState mug_zeroOne
  ν := prodLaw mugHalf
  ν_nonneg := prodLaw_nonneg (fun _ _ => by simp [mugHalf])
  ν_sum_one := sum_prodLaw mugHalf_sum
  U₀ := fun s π => mugU r s (π askT)

/-- **The mugging prior** (definition of record; `udt-bli-sist`, `udt-bli-tiling` and
`udt-paper-tiling` import this name).
Source: bli-slides-034; [[bli-program]] §3.9 U5; mandate §3.7
Kind: D
Fidelity: exact -/
def muggingPrior (r : Bool → ℚ) : FiniteBLIPrior witIndex 1 mugTables Bool :=
  (muggingData r).toPrior

namespace Mugging

variable (r : Bool → ℚ)

/-- The single-point shape of the mugging utility.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma U₀_eq : ∀ (s : Fin 3) (π : Policy mugTables Bool),
    (muggingData r).U₀ s π = mugU r s (π askT) := fun _ _ => rfl

/-- Every point weight is `1/2 > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mugHalf_pos (T : ↥mugTables) (a : Bool) : 0 < mugHalf T a := by simp [mugHalf]

/-- **The one-step value of paying at `Ask`**: `441/10 + (2/100) · r pay`.
Source: bli-slides-034 (`0.49·(−10) + 0.49·100 = 44.1`); [[bli-program]] §3.9 U5
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_ask_pay : (muggingPrior r).EU askT true = 441 / 10 + 2 / 100 * r true := by
  unfold muggingPrior
  rw [(muggingData r).EU_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) true
    (mugHalf_pos _ _)]
  change ∑ s : Fin 3, mugMass s * mugU r s true = _
  rw [Fin.sum_univ_three]
  simp only [mugMass_zero, mugMass_one, mugMass_two, mugU_zero, mugU_one, mugU_two, if_true]
  ring

/-- **The one-step value of refusing at `Ask`**: `(2/100) · r refuse`.
Source: bli-slides-034; [[bli-program]] §3.9 U5
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_ask_refuse : (muggingPrior r).EU askT false = 2 / 100 * r false := by
  unfold muggingPrior
  rw [(muggingData r).EU_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) false
    (mugHalf_pos _ _)]
  change ∑ s : Fin 3, mugMass s * mugU r s false = _
  rw [Fin.sum_univ_three]
  simp only [mugMass_zero, mugMass_one, mugMass_two, mugU_zero, mugU_one, mugU_two,
    Bool.false_eq_true, if_false]
  ring

/-- **One-step UDT pays at `Ask`** for every residual with `|r| ≤ 10`.
Source: [[bli-program]] §3.9 U5 ("one-step UDT pays")
Kind: N+
Fidelity: exact
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem isOneStepChoice_ask_pay (hr : ∀ a, |r a| ≤ 10) :
    (muggingPrior r).IsOneStepChoice askT true := by
  intro b
  cases b
  · rw [EU_ask_refuse, EU_ask_pay]
    have h1 := (abs_le.mp (hr true)).1
    have h2 := (abs_le.mp (hr false)).2
    linarith
  · exact le_rfl

/-- **Refusing at `Ask` is not a one-step choice** for `|r| ≤ 10`.
Source: [[bli-program]] §3.9 U5
Kind: N+
Fidelity: exact
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem not_isOneStepChoice_ask_refuse (hr : ∀ a, |r a| ≤ 10) :
    ¬ (muggingPrior r).IsOneStepChoice askT false := by
  intro h
  have := h true
  rw [EU_ask_refuse, EU_ask_pay] at this
  have h1 := (abs_le.mp (hr true)).1
  have h2 := (abs_le.mp (hr false)).2
  linarith

/-- **The updateful value of paying at `Ask` is `−10`.**
Source: [[bli-program]] §3.9 U5 ("the updateful rule at Ask compares −10 with 0")
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem homeEU_ask_pay : (muggingPrior r).homeEU askT true = -10 := by
  unfold muggingPrior FiniteBLIPrior.homeEU
  rw [(muggingData r).condEU_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) askT true
    (mugHalf_pos _ _)]
  change condExp mugMass (fun s => mugU r s true) (fun s => mugState s = mugState 0) = -10
  rw [condExp_mugState 0 (fun s => mugU r s true)]
  rfl

/-- **The updateful value of refusing at `Ask` is `0`.**
Source: [[bli-program]] §3.9 U5
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem homeEU_ask_refuse : (muggingPrior r).homeEU askT false = 0 := by
  unfold muggingPrior FiniteBLIPrior.homeEU
  rw [(muggingData r).condEU_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) askT false
    (mugHalf_pos _ _)]
  change condExp mugMass (fun s => mugU r s false) (fun s => mugState s = mugState 0) = 0
  rw [condExp_mugState 0 (fun s => mugU r s false)]
  rfl

/-- **The updateful rule refuses at `Ask`.**
Source: [[bli-program]] §3.9 U5 ("and refuses")
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem isUpdatefulChoice_ask_refuse : (muggingPrior r).IsUpdatefulChoice askT false := by
  intro b; cases b
  · exact le_rfl
  · rw [homeEU_ask_pay, homeEU_ask_refuse]; norm_num

/-- **Paying at `Ask` is not an updateful choice.**
Source: [[bli-program]] §3.9 U5
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem not_isUpdatefulChoice_ask_pay : ¬ (muggingPrior r).IsUpdatefulChoice askT true := by
  intro h
  have := h false
  rw [homeEU_ask_pay, homeEU_ask_refuse] at this
  norm_num at this

/-- **The `Rec` branch's value of the `Ask` point**: `100` if it pays, `0` if it refuses.
Source: bli-soto-a-077 / bli-slides-034 (the `Rec` branch's beliefs)
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem condEU_rec_ask (a : Bool) :
    (muggingPrior r).condEU recT askT a = if a then 100 else 0 := by
  unfold muggingPrior
  rw [(muggingData r).condEU_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) recT a
    (mugHalf_pos _ _)]
  change condExp mugMass (fun s => mugU r s a) (fun s => mugState s = mugState 1) = _
  rw [condExp_mugState 1 (fun s => mugU r s a)]
  rfl

/-- The joint mass of a branch and a point is `mugMass · 1/2 > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_pos (i : Fin 3) (T : ↥mugTables) (a : Bool) :
    0 < (muggingPrior r).jointMass (mugState i) T a := by
  unfold muggingPrior
  rw [(muggingData r).jointMass_toPrior]
  change 0 < massOf mugMass (fun s => mugState s = mugState i) * massOf (prodLaw mugHalf) _
  rw [massOf_mugState, IndepData.massOf_prodLaw_point mugHalf mugHalf_sum]
  apply mul_pos
  · fin_cases i <;> norm_num [mugMass]
  · exact mugHalf_pos T a

/-- **`NoCrossBranch` fails on the mugging prior**: the `Rec` cell moves by `100` with the `Ask`
point.
Source: [[bli-program]] §3.9 U5 ("`NoCrossBranch` fails, so U3 does not apply"); §7 item 9
Kind: N−
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem not_noCrossBranch : ¬ (muggingPrior r).NoCrossBranch := by
  intro h
  have := h askT recT true false askT_ne_recT.symm
    (jointMass_pos r 1 askT true) (jointMass_pos r 1 askT false)
  rw [condEU_rec_ask, condEU_rec_ask] at this
  norm_num at this

/-- **`Reflective` holds on the mugging prior** (independent points): the separation of the two
rules is purely cross-branch utility.
Source: mandate T3
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem reflective : (muggingPrior r).Reflective := (muggingData r).reflective_toPrior

/-- `ReflectivePolicy` holds on the mugging prior.
Source: mandate T3
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem reflectivePolicy : (muggingPrior r).ReflectivePolicy :=
  (muggingData r).reflectivePolicy_toPrior

/-- `IndependentPoints` holds on the mugging prior.
Source: mandate T3
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem independentPoints : (muggingPrior r).IndependentPoints :=
  (muggingData r).independentPoints_toPrior_of_prodLaw mugHalf mugHalf_sum rfl

/-- `NDPOL` on the mugging prior.
Source: mandate T3
Kind: N+
Fidelity: exact -/
theorem ndpol : (muggingPrior r).NDPOL :=
  (muggingData r).ndpol_toPrior (fun T a => by
    change 0 < massOf (prodLaw mugHalf) (fun π => π T = a)
    rw [IndepData.massOf_prodLaw_point mugHalf mugHalf_sum]; exact mugHalf_pos T a)

/-- `NDPOLICY` on the mugging prior (every policy has mass `1/8`).
Source: mandate T3
Kind: N+
Fidelity: exact -/
theorem ndpolicy : (muggingPrior r).NDPOLICY :=
  (muggingData r).ndpolicy_toPrior (fun π => prodLaw_pos (fun _ _ => by simp [mugHalf]) π)

/-- `NDHOME` on the mugging prior.
Source: mandate T3
Kind: N+
Fidelity: exact -/
theorem ndhome : (muggingPrior r).NDHOME := by
  rintro ⟨T, hT⟩ a
  simp only [mugTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  · exact jointMass_pos r 0 askT a
  · exact jointMass_pos r 1 recT a
  · exact jointMass_pos r 2 otherT a

/-- **The ex-ante value of any policy** depends on its `Ask` point only:
`441/10 + (2/100) r pay` if it pays at `Ask`, `(2/100) r refuse` otherwise.
Source: bli-slides-034; [[bli-program]] §3.9 U5
Kind: N+
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem exAnteValue_eq (π : Policy mugTables Bool) :
    (muggingPrior r).exAnteValue π =
      if π askT then 441 / 10 + 2 / 100 * r true else 2 / 100 * r false := by
  unfold muggingPrior
  rw [(muggingData r).exAnteValue_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) π
    (prodLaw_pos (fun _ _ => by simp [mugHalf]) π)]
  change ∑ s : Fin 3, mugMass s * mugU r s (π askT) = _
  rw [Fin.sum_univ_three]
  simp only [mugMass_zero, mugMass_one, mugMass_two, mugU_zero, mugU_one, mugU_two]
  cases π askT
  · simp
  · simp; ring

/-- **The constant pay policy is prior-optimal** for `|r| ≤ 10`.
Source: [[bli-program]] §3.9 U9(4) ("the ex-ante optimum also pays"); mandate T6(v)
Kind: N+
Fidelity: exact
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem isPriorOptimal_const_pay (hr : ∀ a, |r a| ≤ 10) :
    (muggingPrior r).IsPriorOptimal (fun _ => true) := by
  intro π'
  rw [exAnteValue_eq, exAnteValue_eq]
  simp only [if_true]
  split_ifs
  · exact le_rfl
  · have h1 := (abs_le.mp (hr true)).1
    have h2 := (abs_le.mp (hr false)).2
    linarith

/-- **Every updateful policy refuses at `Ask` and is beaten by the pay precommitment** by
`441/10 + (2/100)(r pay − r refuse) > 0`; in particular no updateful policy is prior-optimal.
Source: [[bli-program]] §3.9 U5/U9(4) ("the updateful rule fails"); mandate T6(v), (vi)
Kind: N−
Fidelity: exact (the N− for Good's theorem: `LocalUtility` fails here and so does the conclusion)
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem not_isPriorOptimal_of_updateful (hr : ∀ a, |r a| ≤ 10) (π : Policy mugTables Bool)
    (hu : (muggingPrior r).IsUpdatefulPolicy π) :
    (muggingPrior r).exAnteValue π < (muggingPrior r).exAnteValue (fun _ => true) ∧
      ¬ (muggingPrior r).IsPriorOptimal π := by
  have hask : π askT = false := by
    by_contra h
    have h' : π askT = true := by simpa using h
    exact not_isUpdatefulChoice_ask_pay r (h' ▸ hu askT)
  have hlt : (muggingPrior r).exAnteValue π < (muggingPrior r).exAnteValue (fun _ => true) := by
    rw [exAnteValue_eq, exAnteValue_eq, hask]
    simp only [Bool.false_eq_true, if_false, if_true]
    have h1 := (abs_le.mp (hr true)).1
    have h2 := (abs_le.mp (hr false)).2
    linarith
  exact ⟨hlt, fun hopt => lt_irrefl _ (lt_of_lt_of_le hlt (hopt _))⟩

/-- **`LocalUtility` fails on the mugging prior**: at `Rec`, two policies agreeing at `Rec` but
differing at `Ask` have cell values `100` and `0`.
Source: mandate T6(vi); [[bli-program]] §7 item 9
Kind: N−
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem not_localUtility : ¬ (muggingPrior r).LocalUtility := by
  intro h
  have hpos : ∀ π : Policy mugTables Bool, 0 < (muggingPrior r).cellMass recT π := by
    intro π
    unfold muggingPrior
    rw [(muggingData r).cellMass_toPrior]
    change 0 < massOf mugMass (fun s => mugState s = mugState 1) * prodLaw mugHalf π
    rw [massOf_mugState]
    exact mul_pos (by norm_num) (prodLaw_pos (fun _ _ => by simp [mugHalf]) π)
  have hcell : ∀ π : Policy mugTables Bool, (muggingPrior r).cellEU recT π =
      if π askT then 100 else 0 := by
    intro π
    unfold muggingPrior
    rw [(muggingData r).cellEU_single askT (mugU r) (U₀_eq r) recT π
      (prodLaw_pos (fun _ _ => by simp [mugHalf]) π)]
    change condExp mugMass (fun s => mugU r s (π askT)) (fun s => mugState s = mugState 1) = _
    rw [condExp_mugState 1 (fun s => mugU r s (π askT))]
    cases π askT <;> rfl
  have := h recT (fun _ => true) (Function.update (fun _ => true) askT false)
    (by rw [Function.update_of_ne askT_ne_recT.symm]) (hpos _) (hpos _)
  rw [hcell, hcell, Function.update_self] at this
  norm_num at this

end Mugging

end Cleanroom.Bli.UdtBliCore
