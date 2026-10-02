import Cleanroom.Bli.UdtBliSist.Sist
import Mathlib.Tactic.FinCases

/-!
# `udt-bli-sist` · SistWitness: the hand-typed SIST family (T2 c, d, f, h)

The three-table family `sist3Prior w c V ε r₀` over `udt-bli-core`'s `mugTables` (`Ask = (1,0)`,
`Rec = (0,1)`, `Other = (0,0)` on `witIndex`, day 1): base `Fin 3 × Bool` (the state index and a
**noise bit**), masses `w s / 2`, independent uniform points (`prodLaw mugHalf`), Omega's pick
pinned at `Ask`, and the SIST utility with the Ask cost `c ± ε` according to the noise bit, the
Rec reward `V`, and the residual `r₀ (π Ask)`. Everything is parametric; the numbers enter only
through `w`.

* `EU_diff`: `EU Ask give − EU Ask refuse = V·w(Rec) − c·w(Ask) + w(Other)·(r₀ give − r₀ refuse)`,
  by `sist_identity` — the noise averages out (T2(f): the identity is in expectations).
* **The `44.1` instance** (`wPay = (49/100, 49/100, 2/100)`): `isOneStepChoice_pay`, with
  `|r₀| ≤ 10`, and the updateful rule refuses (`isUpdatefulChoice_refuse`).
* **The auditor's alternative table** (`wRefuse = (93/100, 5/100, 2/100)`): the *same* hypotheses
  (shape, positivity, `H_unif`, `H_point`) give `isOneStepChoice_refuse` and
  `not_isOneStepChoice_pay` — the verdict is not in the hypotheses (T2(d)).
* `hUnif`, `hPoint`: both named models are inhabited by this family (one Ask table), and
  `not_classInert_ask`: `ClassInert {Ask} Ask` fails (T2(h)) whenever `V ≠ 0` and `w(Rec) > 0`.

Sources: bli-slides-034, bli-soto-a-077, [[bli-program]] §3.9 U5 and §7 item 9 (the auditor's
table), bli-soto-b-2-011 (ii) (noisy `U`), mandate T2.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging Finset

namespace Sist3

/-! ## The branch predicates on `mugTables` -/

/-- The coin sentence `p` as a day-1 small sentence of `witIndex`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev coin : ↥(witIndex.S 1) := ⟨pW, pW_mem_S1⟩

/-- The second sentence `q` as a day-1 small sentence of `witIndex`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev qS : ↥(witIndex.S 1) := ⟨qW, qW_mem_S1⟩

/-- **The Ask predicate**: the table prices the coin at `1`.
Source: mandate §3.2 (`Ask T := T.1 coin = 1`)
Kind: D
Fidelity: exact -/
def askP (T : ↥mugTables) : Prop := T.1 coin = 1

/-- **The Rec predicate**: the table prices the coin at `0` and `q` at `1` (the `Rec` table).
Source: mandate §3.2 (`Rec T := T.1 coin = 0`, refined by `q` so the residual `(0,0)` is neither)
Kind: D
Fidelity: exact -/
def recP (T : ↥mugTables) : Prop := T.1 coin = 0 ∧ T.1 qS = 1

/-- `askP` is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance askP.decidable : DecidablePred askP := fun T => inferInstanceAs (Decidable (T.1 coin = 1))

/-- `recP` is decidable.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance recP.decidable : DecidablePred recP :=
  fun T => inferInstanceAs (Decidable (T.1 coin = 0 ∧ T.1 qS = 1))

/-- `Ask` is ask-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma askP_askT : askP askT := by simp [askP, mAsk]

/-- `Rec` is not ask-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma not_askP_recT : ¬ askP recT := by simp [askP, mRec]

/-- `Other` is not ask-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma not_askP_otherT : ¬ askP otherT := by simp [askP, mOther]

/-- `Rec` is rec-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma recP_recT : recP recT := by simp [recP, mRec, pW_ne_qW.symm]

/-- `Other` is not rec-like.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma not_recP_otherT : ¬ recP otherT := by simp [recP, mOther]

/-- Every element of `mugTables` is one of the three tables.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eq_three (T : ↥mugTables) : T = askT ∨ T = recT ∨ T = otherT := by
  rcases T with ⟨T, hT⟩
  simp only [mugTables, Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The only ask-like table is `Ask`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma askP_iff (T : ↥mugTables) : askP T ↔ T = askT := by
  rcases eq_three T with rfl | rfl | rfl <;> simp [mAsk_ne_mRec.symm, mAsk_ne_mOther.symm]

/-- `mugState s = Ask ↔ s = 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mugState_eq_askT_iff (s : Fin 3) : mugState s = askT ↔ s = 0 := by
  fin_cases s <;> simp [mAsk_ne_mRec.symm, mAsk_ne_mOther.symm]

/-- `mugState s = Rec ↔ s = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mugState_eq_recT_iff (s : Fin 3) : mugState s = recT ↔ s = 1 := by
  fin_cases s <;> simp [mAsk_ne_mRec, mRec_ne_mOther.symm]

/-! ## The family -/

/-- The noise sign of the noise bit: `+1` or `−1`.
Source: bli-soto-b-2-011 (ii) ("add Gaussian noise to the final utility"; here a two-point noise)
Kind: D
Fidelity: variant: two-point noise in place of Gaussian (disclosed) -/
def noise (n : Bool) : ℚ := if n then 1 else -1

/-- The reference table of the family: an Ask state reads its own table, every other state reads
`Ask` (Omega's pick is pinned at the single Ask table; the residual reads the Ask point).
Source: mandate §3.5; `udt-bli-core` F-13
Kind: D
Fidelity: exact -/
def ref3 (ω : Fin 3 × Bool) : ↥mugTables :=
  if askP (mugState ω.1) then mugState ω.1 else if recP (mugState ω.1) then askT else askT

/-- The payoff of the family: `−(c + ε·noise)` for `give` at Ask, `V` for `give` at Rec, `0` for
`refuse` in both, the residual `r₀ b` elsewhere.
Source: bli-slides-034 (the table `−10, 0, +100, 0`); bli-soto-b-2-011 (ii); mandate T2
Kind: D
Fidelity: exact -/
def pay3 (c V ε : ℚ) (r₀ : Bool → ℚ) (ω : Fin 3 × Bool) (b : Bool) : ℚ :=
  if askP (mugState ω.1) then -(c + ε * noise ω.2) * ind b
  else if recP (mugState ω.1) then V * ind b else r₀ b

variable (w : Fin 3 → ℚ) (hw : ∀ s, 0 ≤ w s) (hw1 : ∑ s, w s = 1) (c V ε : ℚ) (r₀ : Bool → ℚ)

/-- **The three-table SIST data**: base `Fin 3 × Bool` with masses `w s / 2`, the mugging's tables,
`0/1` faith, independent uniform points, the SIST payoff read at `ref3`.
Source: bli-slides-034; mandate T2 (`sistData`)
Kind: D
Fidelity: exact (finite; `w` parametrizes the masses, `ε` the noise, `r₀` the residual) -/
def sist3Data : IndepData witIndex 1 mugTables Bool where
  Ω₀ := Fin 3 × Bool
  μ₀ := fun ω => w ω.1 / 2
  μ₀_nonneg := fun ω => by have := hw ω.1; positivity
  μ₀_sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [← hw1]
    apply Finset.sum_congr rfl
    intro s _
    ring
  state₀ := fun ω => mugState ω.1
  small₀ := fun ω φ => decide ((mugState ω.1).1 φ = 1)
  faith₀ := faith_of_zeroOne _ _ mug_zeroOne
  ν := prodLaw mugHalf
  ν_nonneg := prodLaw_nonneg (fun _ _ => by simp [mugHalf])
  ν_sum_one := sum_prodLaw mugHalf_sum
  U₀ := fun ω π => pay3 c V ε r₀ ω (π (ref3 ω))

/-- **The three-table SIST prior** (the hand-typed N+ family of T2).
Source: bli-slides-034; mandate T2
Kind: D
Fidelity: exact -/
def sist3Prior : FiniteBLIPrior witIndex 1 mugTables Bool := (sist3Data w hw hw1 c V ε r₀).toPrior

/-- The state coordinate of the data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma state₀_eq (ω : Fin 3 × Bool) : (sist3Data w hw hw1 c V ε r₀).state₀ ω = mugState ω.1 :=
  rfl

/-- The base law of the data.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma μ₀_eq (ω : Fin 3 × Bool) : (sist3Data w hw hw1 c V ε r₀).μ₀ ω = w ω.1 / 2 := rfl

/-- Sums over the base are sums over `Fin 3 × Bool` (swaps the `Fintype` instance so that
`Fintype.sum_prod_type` applies).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_base (f : Fin 3 × Bool → ℚ) :
    (∑ ω : (sist3Data w hw hw1 c V ε r₀).Ω₀, f ω) = ∑ ω : Fin 3 × Bool, f ω := rfl

/-- **The family has the SIST shape** with `Ask = askP`, `Rec = recP`, Omega's pick pinned at
`Ask`, observed table `Ask`, cost `c + ε·noise`, reward `V`, residual `r₀`.
Source: mandate T2
Kind: L
Fidelity: exact -/
lemma shaped : SistShaped (sist3Data w hw hw1 c V ε r₀) askP recP (fun _ => askT) askT
    (fun ω => c + ε * noise ω.2) (fun _ => V) (fun _ b => r₀ b) :=
  fun _ _ => rfl

/-- Every point of the family has `ν`-mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_point (T : ↥mugTables) (a : Bool) :
    massOf (sist3Data w hw hw1 c V ε r₀).ν (fun π => π T = a) = 1 / 2 := by
  change massOf (prodLaw mugHalf) (fun π => π T = a) = 1 / 2
  rw [IndepData.massOf_prodLaw_point mugHalf mugHalf_sum]
  rfl

/-- Every policy point of the prior has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_eq (T : ↥mugTables) (a : Bool) : (sist3Prior w hw hw1 c V ε r₀).ppMass T a = 1 / 2 := by
  unfold sist3Prior
  rw [IndepData.ppMass_toPrior, massOf_point]

/-- `δ_Ask(Ask) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pointCorr_ask : pointCorr (sist3Prior w hw hw1 c V ε r₀) askT askT true false = 1 :=
  pointCorr_self _ askT true false (by decide)
    (by rw [ppMass_eq]; norm_num) (by rw [ppMass_eq]; norm_num)

/-- The base mass of each state index is `w s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_state (s : Fin 3) :
    massOf (sist3Data w hw hw1 c V ε r₀).μ₀
      (fun ω => (sist3Data w hw hw1 c V ε r₀).state₀ ω = mugState s) = w s := by
  unfold massOf
  rw [sum_base, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, mugState_injective.eq_iff]
  fin_cases s <;> simp [Fin.sum_univ_three]

/-- **The verdict identity on the family**:
`EU Ask give − EU Ask refuse = V·w(Rec) − c·w(Ask) + w(Other)·(r₀ give − r₀ refuse)`. The noise
`ε` cancels: the identity is in expectations (T2(f)).
Source: bli-slides-034 (`0.49·(−10) + 0.49·100`); bli-soto-b-2-011 (ii); mandate T2(c), (f)
Kind: C (`sist_identity` instantiated and the six base terms summed)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_diff :
    (sist3Prior w hw hw1 c V ε r₀).EU askT true - (sist3Prior w hw hw1 c V ε r₀).EU askT false =
      V * w 1 - c * w 0 + w 2 * (r₀ true - r₀ false) := by
  unfold sist3Prior
  rw [sist_identity _ askP recP (fun _ => askT) askT _ _ _ (shaped w hw hw1 c V ε r₀)
    (by rw [massOf_point]; norm_num) (by rw [massOf_point]; norm_num)]
  have hδ := pointCorr_ask w hw hw1 c V ε r₀
  unfold sist3Prior at hδ
  unfold recTerm askTerm resTerm
  simp only [sum_base, Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, state₀_eq,
    μ₀_eq, mugState_zero, mugState_one, mugState_two, askP_askT, not_askP_recT, not_askP_otherT,
    recP_recT, not_recP_otherT, if_true, if_false, hδ, noise, Bool.false_eq_true, ↓reduceIte]
  ring

/-- **The one-step rule pays** on the family whenever `V·w(Rec) − c·w(Ask)` beats the residual's
swing: `w(Other)·|r₀ give − r₀ refuse| < V·w(Rec) − c·w(Ask)` gives `IsOneStepChoice Ask give` and
the strict verdict.
Source: [[bli-program]] §3.9 U5 ("one-step UDT pays"); mandate T2(c)
Kind: C
Fidelity: exact
Hyps: (a) the stated inequality; does not use faith -/
theorem isOneStepChoice_pay_of (h : w 2 * |r₀ true - r₀ false| < V * w 1 - c * w 0) :
    (sist3Prior w hw hw1 c V ε r₀).IsOneStepChoice askT true ∧
      (sist3Prior w hw hw1 c V ε r₀).EU askT false < (sist3Prior w hw hw1 c V ε r₀).EU askT true := by
  have hd := EU_diff w hw hw1 c V ε r₀
  have hab : w 2 * (r₀ true - r₀ false) ≥ -(w 2 * |r₀ true - r₀ false|) := by
    have := neg_abs_le (r₀ true - r₀ false)
    have hw2 := hw 2
    nlinarith
  refine ⟨fun b => ?_, by linarith⟩
  cases b
  · linarith
  · exact le_rfl

/-- **The one-step rule refuses** on the family whenever `c·w(Ask) − V·w(Rec)` beats the residual's
swing.
Source: [[bli-program]] §7 item 9 (the auditor's alternative table); mandate T2(d)
Kind: C
Fidelity: exact
Hyps: (a) the stated inequality; does not use faith -/
theorem isOneStepChoice_refuse_of (h : w 2 * |r₀ true - r₀ false| < c * w 0 - V * w 1) :
    (sist3Prior w hw hw1 c V ε r₀).IsOneStepChoice askT false ∧
      (sist3Prior w hw hw1 c V ε r₀).EU askT true < (sist3Prior w hw hw1 c V ε r₀).EU askT false := by
  have hd := EU_diff w hw hw1 c V ε r₀
  have hab : w 2 * (r₀ true - r₀ false) ≤ w 2 * |r₀ true - r₀ false| := by
    have := le_abs_self (r₀ true - r₀ false)
    have hw2 := hw 2
    nlinarith
  refine ⟨fun b => ?_, by linarith⟩
  cases b
  · exact le_rfl
  · linarith

/-! ## The updateful value and the inertness failure -/

/-- **The updateful value of paying at `Ask` is `−c`** (the noise averages out), given `w(Ask) > 0`.
Source: [[bli-program]] §3.9 U5 ("the updateful rule at Ask compares −10 with 0")
Kind: N+
Fidelity: exact
Hyps: (a) `0 < w 0`; does not use faith -/
theorem homeEU_ask (hw0 : 0 < w 0) (a : Bool) :
    (sist3Prior w hw hw1 c V ε r₀).homeEU askT a = -c * ind a := by
  unfold sist3Prior
  rw [homeEU_ref_self _ _ _ (shaped w hw hw1 c V ε r₀) askT a
    (fun ω hω => by
      simp only [state₀_eq] at hω
      unfold sistRef
      simp [hω])
    (by rw [massOf_point]; norm_num)]
  unfold condExp integralOf massOf
  rw [sum_base, sum_base, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [state₀_eq, μ₀_eq, Fintype.sum_bool, mugState_eq_askT_iff, Fin.sum_univ_three]
  unfold sistPay
  simp only [state₀_eq, mugState_zero, mugState_one, mugState_two, askP_askT, not_askP_recT,
    not_askP_otherT, if_true, if_false, noise]
  simp
  field_simp
  ring

/-- **The updateful rule refuses at `Ask`** when `c > 0` and `w(Ask) > 0`.
Source: [[bli-program]] §3.9 U5 ("and refuses")
Kind: N+
Fidelity: exact
Hyps: (a) `0 < c`, `0 < w 0`; does not use faith -/
theorem isUpdatefulChoice_refuse (hw0 : 0 < w 0) (hc : 0 < c) :
    (sist3Prior w hw hw1 c V ε r₀).IsUpdatefulChoice askT false ∧
      ¬ (sist3Prior w hw hw1 c V ε r₀).IsUpdatefulChoice askT true := by
  constructor
  · intro b
    rw [homeEU_ask w hw hw1 c V ε r₀ hw0, homeEU_ask w hw hw1 c V ε r₀ hw0]
    cases b <;> simp <;> linarith
  · intro h
    have := h false
    rw [homeEU_ask w hw hw1 c V ε r₀ hw0, homeEU_ask w hw hw1 c V ε r₀ hw0] at this
    simp at this
    linarith

/-- **The `Rec` branch's value of the `Ask` point is `V·[give]`** (given `w(Rec) > 0`).
Source: bli-soto-a-077 (the Rec branch's beliefs); mandate T2(h)
Kind: N+
Fidelity: exact
Hyps: (a) `0 < w 1`; does not use faith -/
theorem condEU_rec (hw1' : 0 < w 1) (a : Bool) :
    (sist3Prior w hw hw1 c V ε r₀).condEU recT askT a = V * ind a := by
  unfold sist3Prior
  rw [condEU_ref _ _ _ (shaped w hw hw1 c V ε r₀) recT askT a]
  have hmass : 0 < massOf (sist3Data w hw hw1 c V ε r₀).μ₀
      (fun ω => (sist3Data w hw hw1 c V ε r₀).state₀ ω = recT) := by
    rw [← mugState_one, massOf_state]; exact hw1'
  have hpp : 0 < (sist3Data w hw hw1 c V ε r₀).toPrior.ppMass askT a := by
    rw [IndepData.ppMass_toPrior, massOf_point]; norm_num
  unfold condExp
  rw [integralOf_congr_fun _ _ (fun _ => V * ind a) _ (by
    intro ω hω
    simp only [state₀_eq] at hω
    unfold sistRef sistPay
    simp only [state₀_eq, hω, not_askP_recT, recP_recT, if_true, if_false,
      condPoint_self _ askT _ a hpp, Fintype.sum_bool]
    cases a <;> simp)]
  rw [integralOf_const, mul_div_assoc, div_self (ne_of_gt hmass), mul_one]

/-- The joint mass of a base state and a point is `w s / 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma jointMass_eq (s : Fin 3) (T : ↥mugTables) (a : Bool) :
    (sist3Prior w hw hw1 c V ε r₀).jointMass (mugState s) T a = w s / 2 := by
  unfold sist3Prior
  rw [IndepData.jointMass_toPrior, massOf_state, massOf_point]
  ring

/-- **`ClassInert {Ask} Ask` fails on the family** whenever `V ≠ 0` and `w(Rec) > 0`: the Rec
branch's value of the Ask point moves by `V` with the point (T2(h)).
Source: [[bli-program]] §3.9 U5 ("`NoCrossBranch` fails"); mandate T2(h)
Kind: N−
Fidelity: exact
Hyps: (a) `V ≠ 0`, `0 < w 1`; does not use faith -/
theorem not_classInert_ask (hw1' : 0 < w 1) (hV : V ≠ 0) :
    ¬ ClassInert (sist3Prior w hw hw1 c V ε r₀) {askT} askT := by
  intro h
  have hrec : recT ∉ ({askT} : Finset ↥mugTables) := by
    simp only [Finset.mem_singleton]
    exact askT_ne_recT.symm
  have hj : ∀ a, 0 < (sist3Prior w hw hw1 c V ε r₀).jointMass recT askT a := by
    intro a
    rw [← mugState_one, jointMass_eq]
    linarith
  have := h recT hrec true false (hj true) (hj false)
  rw [condEU_rec w hw hw1 c V ε r₀ hw1', condEU_rec w hw hw1 c V ε r₀ hw1'] at this
  simp at this
  exact hV this

/-! ## The named models are inhabited -/

/-- **`H_unif` holds on the family** (one ask-like table).
Source: bli-soto-a-2-013 (`H_unif`); mandate T2(c)
Kind: N− (degenerate as an instance of `H_unif`: the Ask class is the singleton `{Ask}`, so the
constancy is `pp ω Ask = pp ω Ask`; the non-degenerate `H_unif` instance is `TentSist.hUnif` with
three Ask tables, and the two-ask-table family of `SymWitness.lean` is the one where `H_unif`
fails)
Fidelity: exact
Hyps: (a) none -/
theorem hUnif : HUnif (sist3Prior w hw hw1 c V ε r₀) askP askT := by
  intro ω _ T hT
  rw [(askP_iff T).mp hT]

/-- **`H_point` holds on the family** (one ask-like table).
Source: bli-soto-a-2-013 (`H_point`); mandate T2(b)
Kind: N− (degenerate: the Ask class is the singleton `{Ask}`, so "no other Ask table has mass"
holds with no content; the package ships no non-degenerate inhabitant of `H_point` — the tent has
three Ask tables of mass `1/9` and the two-ask-table family has `Ask₂` of positive mass, and both
fail it)
Fidelity: exact
Hyps: (a) none -/
theorem hPoint : HPoint (sist3Prior w hw hw1 c V ε r₀) askP askT := by
  intro T hT hne
  exact absurd ((askP_iff T).mp hT) hne

/-- **The family is `Reflective`, `IndependentPoints`, `NDPOL` and `NDPOLICY`** (independent
uniform points).
Source: mandate T2 (structural facts of the N+)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem structure_facts :
    (sist3Prior w hw hw1 c V ε r₀).Reflective ∧ (sist3Prior w hw hw1 c V ε r₀).IndependentPoints ∧
      (sist3Prior w hw hw1 c V ε r₀).NDPOL ∧ (sist3Prior w hw hw1 c V ε r₀).NDPOLICY := by
  refine ⟨(sist3Data w hw hw1 c V ε r₀).reflective_toPrior,
    (sist3Data w hw hw1 c V ε r₀).independentPoints_toPrior_of_prodLaw mugHalf mugHalf_sum rfl,
    fun T a => by rw [ppMass_eq]; norm_num,
    (sist3Data w hw hw1 c V ε r₀).ndpolicy_toPrior (fun π => prodLaw_pos (fun _ _ => by
      simp [mugHalf]) π)⟩

/-! ## The two instances -/

/-- The source's masses `(49/100, 49/100, 2/100)`.
Source: bli-slides-034 ("49% each", 2% residual)
Kind: D
Fidelity: exact -/
def wPay : Fin 3 → ℚ
  | 0 => 49 / 100
  | 1 => 49 / 100
  | 2 => 2 / 100

/-- The auditor's masses `(93/100, 5/100, 2/100)`.
Source: [[bli-program]] §7 item 9; mandate T2(d)
Kind: D
Fidelity: exact -/
def wRefuse : Fin 3 → ℚ
  | 0 => 93 / 100
  | 1 => 5 / 100
  | 2 => 2 / 100

/-- `wPay` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wPay_nonneg : ∀ s, 0 ≤ wPay s := by intro s; fin_cases s <;> norm_num [wPay]

/-- `wPay` sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wPay_sum : ∑ s, wPay s = 1 := by rw [Fin.sum_univ_three]; norm_num [wPay]

/-- `wRefuse` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wRefuse_nonneg : ∀ s, 0 ≤ wRefuse s := by intro s; fin_cases s <;> norm_num [wRefuse]

/-- `wRefuse` sums to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wRefuse_sum : ∑ s, wRefuse s = 1 := by rw [Fin.sum_univ_three]; norm_num [wRefuse]

/-- **The `44.1` instance**: at `(49/100, 49/100, 2/100)`, `(100, 10)`, any noise `ε` and any
residual with `|r₀| ≤ 10`, the one-step rule pays (strictly) and the updateful rule refuses; the
exact difference is `441/10 + (2/100)·(r₀ give − r₀ refuse)`.
Source: bli-slides-034; bli-soto-a-077; [[bli-program]] §3.9 U5; mandate T2(c)
Kind: N+
Fidelity: exact
Hyps: (a) `|r₀| ≤ 10`; does not use faith -/
theorem pay_instance (ε : ℚ) (r₀ : Bool → ℚ) (hr : ∀ a, |r₀ a| ≤ 10) :
    (sist3Prior wPay wPay_nonneg wPay_sum 10 100 ε r₀).EU askT true -
        (sist3Prior wPay wPay_nonneg wPay_sum 10 100 ε r₀).EU askT false =
        441 / 10 + 2 / 100 * (r₀ true - r₀ false) ∧
      (sist3Prior wPay wPay_nonneg wPay_sum 10 100 ε r₀).IsOneStepChoice askT true ∧
      (sist3Prior wPay wPay_nonneg wPay_sum 10 100 ε r₀).EU askT false <
        (sist3Prior wPay wPay_nonneg wPay_sum 10 100 ε r₀).EU askT true ∧
      (sist3Prior wPay wPay_nonneg wPay_sum 10 100 ε r₀).IsUpdatefulChoice askT false ∧
      ¬ (sist3Prior wPay wPay_nonneg wPay_sum 10 100 ε r₀).IsUpdatefulChoice askT true := by
  have hab : |r₀ true - r₀ false| ≤ 20 := by
    have h1 := abs_le.mp (hr true)
    have h2 := abs_le.mp (hr false)
    rw [abs_le]; constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [EU_diff]; norm_num [wPay]
  · exact (isOneStepChoice_pay_of wPay wPay_nonneg wPay_sum 10 100 ε r₀
      (by norm_num [wPay]; linarith)).1
  · exact (isOneStepChoice_pay_of wPay wPay_nonneg wPay_sum 10 100 ε r₀
      (by norm_num [wPay]; linarith)).2
  · exact isUpdatefulChoice_refuse wPay wPay_nonneg wPay_sum 10 100 ε r₀ (by norm_num [wPay])
      (by norm_num)

/-- **The auditor's alternative table**: at `(93/100, 5/100, 2/100)` — the *same* shape, the same
positivity, `H_unif` and `H_point` — the one-step rule refuses (strictly) for every `|r₀| ≤ 10`;
the exact difference is `−43/10 + (2/100)·(r₀ give − r₀ refuse)`. The verdict is not in the
hypotheses.
Source: [[bli-program]] §7 item 9 ("the auditor's test is a table under which the same hypotheses
yield refuse"); mandate T2(d)
Kind: N+
Fidelity: exact
Hyps: (a) `|r₀| ≤ 10`; does not use faith -/
theorem refuse_instance (ε : ℚ) (r₀ : Bool → ℚ) (hr : ∀ a, |r₀ a| ≤ 10) :
    (sist3Prior wRefuse wRefuse_nonneg wRefuse_sum 10 100 ε r₀).EU askT true -
        (sist3Prior wRefuse wRefuse_nonneg wRefuse_sum 10 100 ε r₀).EU askT false =
        -43 / 10 + 2 / 100 * (r₀ true - r₀ false) ∧
      (sist3Prior wRefuse wRefuse_nonneg wRefuse_sum 10 100 ε r₀).IsOneStepChoice askT false ∧
      (sist3Prior wRefuse wRefuse_nonneg wRefuse_sum 10 100 ε r₀).EU askT true <
        (sist3Prior wRefuse wRefuse_nonneg wRefuse_sum 10 100 ε r₀).EU askT false ∧
      ¬ (sist3Prior wRefuse wRefuse_nonneg wRefuse_sum 10 100 ε r₀).IsOneStepChoice askT true := by
  have hab : |r₀ true - r₀ false| ≤ 20 := by
    have h1 := abs_le.mp (hr true)
    have h2 := abs_le.mp (hr false)
    rw [abs_le]; constructor <;> linarith
  have hmain := isOneStepChoice_refuse_of wRefuse wRefuse_nonneg wRefuse_sum 10 100 ε r₀
    (by norm_num [wRefuse]; linarith)
  refine ⟨?_, hmain.1, hmain.2, ?_⟩
  · rw [EU_diff]; norm_num [wRefuse]
  · intro h
    have := h false
    linarith [hmain.2]

end Sist3

end Cleanroom.Bli.UdtBliSist
