import Cleanroom.Bli.BliExtrapolation.Witnesses

/-!
# `bli-extrapolation` · Refutations: the two hidden-universal witnesses (target 4d, N+, `refuted`)

PDF 07 p. 2 / PIBBSS §4.3 p. 18: "We also get the other inequality …, because
`lim_m P(¬∀mφ(m) ∧ ⋀_m φ(i)) = 0`. Indeed, the latter could only fail if a finite and
`Ax`-consistent `C ∧ ¬∀mφ(m)` propositionally entailed infinitely many `φ(i)`. This isn't possible
with our `Ax`, because the only way to have this is through quantification." Both witnesses
below are exactly such a `C`, built from PDF 07's schema 1 with schema 2 *empty* (`split = ∅`;
no third schema), with a base satisfying `BaseAxConsistent` and positive mass on `C`;
`gaifman_lt_of_hiddenUniversal` then gives `μ(∀mφ) < μ(⋂ φ(i))` strictly. Adding schema-2
axioms can only shrink the `Ax`-worlds, so the Lean does not by itself show the hidden
conjunction survives a non-empty schema 2; that step is 2-006 (i)'s prose construction (the
splitting schema relates universals of conjunctions, which `U`, `U'` are not).

**Polarity.** Both structures have `pol = true` (the universal *is* its atom), while FAF's
first-order universals are `pol = false` (`∀ = ∼∃¬`, design decision 1). The refuted reading
quantifies over every quantifier structure, so one `pol = true` counterexample refutes it; a
`pol = false` twin is the same construction with the universal atoms' truth values flipped
(`holds_univSentence` handles both polarities), and is not written out.

* **`refute_second_inequality`** ([[bli-soto-a-2-inventory]] 006): universals `U = ∀mφ(m)`,
  `U' = ∀m¬¬φ(m)` with instances `a_i` and `∼∼a_i`; `C = ¬U ∧ U'` has base mass `¼` and
  `Ax`-entails every `a_i` through schema 1 on `U'`.
* **`refute_propagation`** ([[bli-soto-a-inventory]] 057 (ii)): universals `U = ∀mφ(m)`,
  `U'' = ∀m(φ(m) ↔ φ(m+1))` with instances `a_i` and `(a_i → a_{i+1}) ∧ (a_{i+1} → a_i)`;
  `C = ¬U ∧ a_0 ∧ U''` has base mass `⅛` and entails every `a_i` by induction. PDF 07 states this
  one correctly and files it against a *propagation* schema; the finding is that the same
  mechanism already lives in plain `Ax` (the first witness).

Reading formalized (ATTRIBUTION-UNVETTED, see the findings file): "for every abstract quantifier
structure, enumeration, `Ax`-consistent base and universal, equality holds". Surviving neighbour:
`gaifman_eq_of_halving` (4b).
-/

namespace Cleanroom.Bli.BliExtrapolation

open LogicalInduction LO.Propositional BoolPCWorld MeasureTheory Finset Cleanroom.Bli.BliFound
open Classical

/-! ## The 2-006 witness -/

/-- **The 2-006 structure**: `U = univAtom 0` with instances `a_i = instAtom i`, and
`U' = univAtom 1` with instances `∼∼a_i`.
Source: [[bli-soto-a-2-inventory]] 006
Kind: D
Fidelity: n/a -/
def refS : UnivStructure :=
  mkStructure (fun i => Formula.atom (instAtom i)) (fun i => ∼∼Formula.atom (instAtom i))

/-- The enumeration with `U` at `0` and `U'` at `1` (`(swap 1 2) ∘ freshEnum`).
Source: [[bli-soto-a-2-inventory]] 006
Kind: D
Fidelity: n/a -/
noncomputable def refEnum : ℕ ≃ ℕ := (Equiv.swap 1 2).trans freshEnum

/-- `refEnum 0 = univAtom 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refEnum_zero : refEnum 0 = univAtom 0 := by
  simp [refEnum, Equiv.swap_apply_of_ne_of_ne, freshEnum_zero]

/-- `refEnum 1 = univAtom 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refEnum_one : refEnum 1 = univAtom 1 := by
  simp [refEnum, Equiv.swap_apply_left, freshEnum_two]

/-- The 2-006 base: uniform on `{U, U'}` (`B = 2`, each conjunction `¼`).
Source: [[bli-soto-a-2-inventory]] 006 ("`q` uniform on `{U, U'}`, `B = 2`")
Kind: D
Fidelity: n/a -/
def refBase : FiniteWorld 2 → ℚ := chainPMF halfRule 2

/-- The 2-006 base is `¼` everywhere.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma refBase_apply (w : FiniteWorld 2) : refBase w = 1 / 4 := by
  unfold refBase
  simp only [chainPMF, halfRule]
  split_ifs <;> norm_num

/-- Every level-`2` conjunction is `Ax`-consistent for `refS` (make every `a_i` true).
Source: [[bli-soto-a-2-inventory]] 006 (i)
Kind: N+
Fidelity: n/a -/
theorem ref_baseAxConsistent : BaseAxConsistent refS refEnum refBase := by
  intro w _
  refine ⟨(fun a => if a = univAtom 0 then (w 0 = true) else if a = univAtom 1 then (w 1 = true)
    else True : PCWorld), ?_, ?_⟩
  · rw [refS, mk_axHolds_iff]
    refine ⟨fun i _ => ?_, fun i _ => ?_⟩
    · rw [PCWorld.holds_atom]
      simp [(univAtom_ne_instAtom 0 i).symm, (univAtom_ne_instAtom 1 i).symm]
    · rw [PCWorld.holds_neg, PCWorld.holds_neg, PCWorld.holds_atom]
      simp [(univAtom_ne_instAtom 0 i).symm, (univAtom_ne_instAtom 1 i).symm]
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    subst hφ
    rw [conj_holds_iff, Fin.forall_fin_succ, Fin.forall_fin_one]
    have h01 : univAtom 1 ≠ univAtom 0 := fun h => by
      have := univAtom_injective h; omega
    constructor
    · simp [refEnum_zero]
    · simp [refEnum_one, h01]

/-- The hidden conjunction `C = ¬U ∧ U'`.
Source: [[bli-soto-a-2-inventory]] 006
Kind: D
Fidelity: n/a -/
def refC : FiniteWorld 2 := ![false, true]

/-- `U`'s level under `refEnum` is `1 ≤ 2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ref_lev : level refEnum (refS.univSentence 0) ≤ 2 := by simp [refS, ← refEnum_zero]

/-- `C` refutes `U`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ref_notU : ¬ (enumWorld refEnum refC).toPCWorld.Holds (refS.univSentence 0) := by
  simp only [refS, mk_univSentence, PCWorld.holds_atom, BoolPCWorld.toPCWorld, ← refEnum_zero]
  have h := enumWorld_apply_e refEnum refC (0 : Fin 2)
  simp only [Fin.val_zero] at h
  rw [h]
  simp [refC]

/-- `C = ¬U ∧ U'` `Ax`-entails every `a_i` (schema 1 on `U'` gives `¬¬a_i`).
Source: [[bli-soto-a-2-inventory]] 006 (ii)
Kind: P
Fidelity: n/a -/
lemma ref_entails (i : ℕ) : AxEntails refS {conj refEnum refC} (refS.inst 0 i) := by
  intro v hv hΓ
  have hconj : v.Holds (conj refEnum refC) := hΓ _ (Finset.mem_singleton_self _)
  rw [conj_holds_iff] at hconj
  have h1 := hconj 1
  simp only [refC, Matrix.cons_val_one] at h1
  rw [show ((1 : Fin 2) : ℕ) = 1 from rfl, refEnum_one] at h1
  have hU' : v (univAtom 1) := h1.mpr rfl
  rw [refS, mk_axHolds_iff] at hv
  have := hv.2 i hU'
  simp only [refS, mk_inst_zero]
  rw [PCWorld.holds_neg, PCWorld.holds_neg] at this
  exact not_not.mp this

/-- The chained mass of `C` is its base mass `¼`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sotoPMF_refC : sotoPMF refS refEnum refBase 2 refC = 1 / 4 := by
  have h := sotoPMF_base refS refEnum (q := refBase) (chainPMF_nonneg halfRule_inUnit 2)
    (chainPMF_sum_one halfRule 2) refC
  rw [h, refBase_apply]

/-- **`C = ¬U ∧ U'` is a hidden universal** for `refS`: positive base mass `¼`, refutes `U`, and
`Ax`-entails every `a_i`.
Source: [[bli-soto-a-2-inventory]] 006 (i)–(iii)
Kind: N+
Fidelity: n/a -/
theorem ref_hiddenUniversal : HiddenUniversal refS refEnum refBase 0 := by
  refine ⟨2, refC, ?_, ref_lev, ref_notU, ref_entails⟩
  rw [sotoPMF_refC]
  norm_num

/-- The 2-006 witness's extrapolation.
Source: [[bli-soto-a-2-inventory]] 006
Kind: D
Fidelity: n/a -/
noncomputable def refMeasure : Measure BoolPCWorld :=
  extrapolate refS refEnum refBase (chainPMF_nonneg halfRule_inUnit 2)

/-- Under the 2-006 witness, `P(U) = ½`.
Source: [[bli-soto-a-2-inventory]] 006
Kind: N+
Fidelity: n/a -/
theorem ref_val_univ : extrapolateVal refS refEnum refBase (refS.univSentence 0) = 1 / 2 := by
  unfold refBase
  rw [extrapolateVal_of_chainBase refS refEnum halfRule_inUnit 2 (by simp [refS, ← refEnum_zero])]
  simp [refS, chainVal_half_atom]

/-- **`refute_second_inequality`** (4d, N+, `refuted`): for the 2-006 structure, enumeration and
base, `μ U = ½`, the event "`¬U` and every instance" has measure at least `¼`, and
`μ U < μ (⋂ i, I_i)` **strictly**. The sources' second inequality
`P(∀mφ(m)) ≥ lim_m P(⋀_{i≤m} φ(i))` is false, and the stated reason ("the only way to have this is
through quantification") is false: `¬∀mφ(m) ∧ ∀m¬¬φ(m)` is `Ax`-consistent and entails every
`φ(i)` through `Ax`'s own schema 1. PDF 07's schema 1 with schema 2 empty (`split = ∅`), a
`BaseAxConsistent` base with positive mass on the hidden conjunction.
Source: PDF 07 p. 2 / PIBBSS §4.3 p. 18 ("We also get the other inequality … This isn't possible
with our `Ax`, because the only way to have this is through quantification");
[[bli-soto-a-2-inventory]] 006; [[bli-soto-a-inventory]] 052 (v)
Kind: N+
Fidelity: exact (refutation of the stated sentence under the abstract layer; the first-order
version is target 8's)
Hyps: (a) none (all discharged) -/
theorem refute_second_inequality :
    refMeasure (univEvent refS 0) = ENNReal.ofReal (1 / 2) ∧
    ENNReal.ofReal (1 / 4) ≤ refMeasure ((univEvent refS 0)ᶜ ∩ ⋂ i, instEvent refS 0 i) ∧
    refMeasure (univEvent refS 0) < refMeasure (⋂ i, instEvent refS 0 i) := by
  have hq0 := chainPMF_nonneg halfRule_inUnit 2
  have hq1 := chainPMF_sum_one halfRule 2
  refine ⟨?_, ?_, ?_⟩
  · unfold refMeasure univEvent
    rw [extrapolate_sentence, ref_val_univ]
    norm_num
  · unfold refMeasure
    have h := hidden_le_measure refS refEnum refBase 0 hq0 hq1 ref_baseAxConsistent 2 refC
      ref_lev ref_notU ref_entails
    rw [sotoPMF_refC] at h
    have h' : ENNReal.ofReal (1 / 4) ≤
        (extrapolate refS refEnum refBase hq0) ((univEvent refS 0)ᶜ ∩ ⋂ i, instEvent refS 0 i) := by
      convert h using 2; norm_num
    exact h'
  · unfold refMeasure
    exact gaifman_lt_of_hiddenUniversal refS refEnum refBase 0 hq0 hq1 ref_baseAxConsistent
      ref_hiddenUniversal

/-! ## The propagation witness (057 (ii)) -/

/-- **The propagation structure**: `U = univAtom 0` with instances `a_i`, and `U'' = univAtom 1`
with instances `(a_i → a_{i+1}) ∧ (a_{i+1} → a_i)`.
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: D
Fidelity: n/a -/
def propS : UnivStructure :=
  mkStructure (fun i => Formula.atom (instAtom i))
    (fun i => (Formula.atom (instAtom i) 🡒 Formula.atom (instAtom (i + 1))) ⋏
      (Formula.atom (instAtom (i + 1)) 🡒 Formula.atom (instAtom i)))

/-- The enumeration with `U` at `0`, `a_0` at `1`, `U''` at `2` (`(swap 1 4) ∘ freshEnum`).
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: D
Fidelity: n/a -/
noncomputable def propEnum : ℕ ≃ ℕ := (Equiv.swap 1 4).trans freshEnum

/-- `propEnum 0 = univAtom 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma propEnum_zero : propEnum 0 = univAtom 0 := by
  simp [propEnum, Equiv.swap_apply_of_ne_of_ne, freshEnum_zero]

/-- `propEnum 1 = instAtom 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma propEnum_one : propEnum 1 = instAtom 0 := by
  simp [propEnum, Equiv.swap_apply_left, freshEnum_four]

/-- `propEnum 2 = univAtom 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma propEnum_two : propEnum 2 = univAtom 1 := by
  simp [propEnum, Equiv.swap_apply_of_ne_of_ne, freshEnum_two]

/-- The propagation base rule: `U` with probability `½`; `a_0` certain given `U`, `½` given `¬U`;
`U''` with probability `½`. It gives no mass to `U ∧ ¬a_0`, the one `Ax`-inconsistent pattern
among the first three atoms.
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: D
Fidelity: n/a -/
def propRule : CondRule := fun k u =>
  if h : k = 1 then (if u ⟨0, by omega⟩ = true then 1 else 1 / 2) else 1 / 2

/-- `propRule` takes values in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma propRule_inUnit : propRule.InUnit := by
  intro k u
  unfold propRule
  split_ifs <;> norm_num

/-- The propagation base: the chain of `propRule` at level `3`.
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: D
Fidelity: n/a -/
def propBase : FiniteWorld 3 → ℚ := chainPMF propRule 3

/-- The propagation base charges `U ∧ ¬a_0` with nothing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma propBase_zero_of (w : FiniteWorld 3) (h0 : w 0 = true) (h1 : w 1 = false) :
    propBase w = 0 := by
  have hw : w = (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 (w 0)) (w 1)) (w 2) : FiniteWorld 3) := by
    ext i; fin_cases i <;> rfl
  rw [hw, h0, h1]
  unfold propBase
  rw [chainPMF_snoc, chainPMF_snoc, chainPMF_snoc]
  simp [propRule, Fin.snoc]

/-- The hidden conjunction `C = ¬U ∧ a_0 ∧ U''`.
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: D
Fidelity: n/a -/
def propC : FiniteWorld 3 := ![false, true, true]

/-- The hidden conjunction has base mass `⅛`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma propBase_propC : propBase propC = 1 / 8 := by
  have hC : propC = (Fin.snoc (Fin.snoc (Fin.snoc Fin.elim0 false) true) true : FiniteWorld 3) := by
    ext i; fin_cases i <;> rfl
  rw [hC]
  unfold propBase
  rw [chainPMF_snoc, chainPMF_snoc, chainPMF_snoc]
  simp [propRule, Fin.snoc, chainPMF]
  norm_num

/-- The propagation base is `Ax`-consistent: a base world of positive mass has `¬(U ∧ ¬a_0)`,
and the world reading `U`, `U''` as the base does and every `a_i` as `a_0` satisfies both schema
families.
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: N+
Fidelity: n/a -/
theorem prop_baseAxConsistent : BaseAxConsistent propS propEnum propBase := by
  intro w hw
  have hpat : ¬ (w 0 = true ∧ w 1 = false) := fun h => hw (propBase_zero_of w h.1 h.2)
  refine ⟨(fun a => if a = univAtom 0 then (w 0 = true) else if a = univAtom 1 then (w 2 = true)
    else (w 1 = true) : PCWorld), ?_, ?_⟩
  · rw [propS, mk_axHolds_iff]
    refine ⟨fun i hU => ?_, fun i _ => ?_⟩
    · rw [PCWorld.holds_atom]
      simp only [(univAtom_ne_instAtom 0 i).symm, (univAtom_ne_instAtom 1 i).symm, if_false]
      simp only [if_true] at hU
      cases h1 : w 1
      · exact absurd ⟨hU, h1⟩ hpat
      · rfl
    · rw [PCWorld.holds_and, holds_imp, holds_imp, PCWorld.holds_atom, PCWorld.holds_atom]
      simp [(univAtom_ne_instAtom 0 i).symm, (univAtom_ne_instAtom 1 i).symm,
        (univAtom_ne_instAtom 0 (i + 1)).symm, (univAtom_ne_instAtom 1 (i + 1)).symm]
  · intro φ hφ
    rw [Finset.mem_singleton] at hφ
    subst hφ
    rw [conj_holds_iff, Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_one]
    have h01 : univAtom 1 ≠ univAtom 0 := fun h => by
      have := univAtom_injective h; omega
    refine ⟨?_, ?_, ?_⟩
    · simp [propEnum_zero]
    · simp [propEnum_one, (univAtom_ne_instAtom 0 0).symm, (univAtom_ne_instAtom 1 0).symm]
    · simp [propEnum_two, h01]

/-- `U`'s level under `propEnum` is `1 ≤ 3`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prop_lev : level propEnum (propS.univSentence 0) ≤ 3 := by simp [propS, ← propEnum_zero]

/-- `C` refutes `U`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prop_notU : ¬ (enumWorld propEnum propC).toPCWorld.Holds (propS.univSentence 0) := by
  simp only [propS, mk_univSentence, PCWorld.holds_atom, BoolPCWorld.toPCWorld, ← propEnum_zero]
  have h := enumWorld_apply_e propEnum propC (0 : Fin 3)
  simp only [Fin.val_zero] at h
  rw [h]
  simp [propC]

/-- `C = ¬U ∧ a_0 ∧ U''` `Ax`-entails every `a_i` by induction (schema 1 on `U''` gives
`a_i ↔ a_{i+1}`).
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: P
Fidelity: n/a -/
lemma prop_entails (i : ℕ) : AxEntails propS {conj propEnum propC} (propS.inst 0 i) := by
  intro v hv hΓ
  have hconj : v.Holds (conj propEnum propC) := hΓ _ (Finset.mem_singleton_self _)
  rw [conj_holds_iff] at hconj
  have h1 := hconj 1
  have h2 := hconj 2
  simp only [propC, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h1 h2
  rw [show ((1 : Fin 3) : ℕ) = 1 from rfl, propEnum_one] at h1
  rw [show ((2 : Fin 3) : ℕ) = 2 from rfl, propEnum_two] at h2
  have ha0 : v (instAtom 0) := by simpa using h1
  have hU'' : v (univAtom 1) := by simpa using h2
  rw [propS, mk_axHolds_iff] at hv
  simp only [propS, mk_inst_zero, PCWorld.holds_atom]
  induction i with
  | zero => exact ha0
  | succ i ih =>
      have := hv.2 i hU''
      rw [PCWorld.holds_and] at this
      exact this.1 ih

/-- The chained mass of `C` is its base mass `⅛`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sotoPMF_propC : sotoPMF propS propEnum propBase 3 propC = 1 / 8 := by
  have h := sotoPMF_base propS propEnum (q := propBase) (chainPMF_nonneg propRule_inUnit 3)
    (chainPMF_sum_one propRule 3) propC
  rw [h, propBase_propC]

/-- **`C = ¬U ∧ a_0 ∧ U''` is a hidden universal** for `propS`: base mass `⅛`, refutes `U`, and
`Ax`-entails every `a_i`.
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: N+
Fidelity: n/a -/
theorem prop_hiddenUniversal : HiddenUniversal propS propEnum propBase 0 := by
  refine ⟨3, propC, ?_, prop_lev, prop_notU, prop_entails⟩
  rw [sotoPMF_propC]
  norm_num

/-- The propagation witness's extrapolation.
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: D
Fidelity: n/a -/
noncomputable def propMeasure : Measure BoolPCWorld :=
  extrapolate propS propEnum propBase (chainPMF_nonneg propRule_inUnit 3)

/-- Under the propagation witness, `P(U) = ½`.
Source: [[bli-soto-a-inventory]] 057 (ii)
Kind: N+
Fidelity: n/a -/
theorem prop_val_univ : extrapolateVal propS propEnum propBase (propS.univSentence 0) = 1 / 2 := by
  unfold propBase
  rw [extrapolateVal_of_chainBase propS propEnum propRule_inUnit 3
    (by simp [propS, ← propEnum_zero])]
  have h1 : chainVal propEnum propRule (propS.univSentence 0) =
      chainVal propEnum propRule (⊤ ⋏ Formula.atom (propEnum 0)) := by
    apply chainVal_congr
    intro v
    simp [propS, PCWorld.holds_and, PCWorld.holds_top, propEnum_zero]
  rw [h1, chainVal_and_atom propEnum _ (by simp) (1 / 2) (fun _ _ => Or.inr (by simp [propRule])),
    chainVal_top]
  ring

/-- **`refute_propagation`** (4d, N+, second instance): for the propagation structure, `μ U = ½`,
the event "`¬U` and every instance" has measure at least `⅛`, and `μ U < μ (⋂ i, I_i)` strictly.
PDF 07 states this counterexample correctly and files it against a *propagation* schema; the same
mechanism lives in plain `Ax` (`refute_second_inequality`).
Source: PDF 07 pp. 3–4 ("Propagation": "`φ(1) ∧ ∀m(φ(m) ↔ φ(m+1)) ∧ ¬∀mφ(m)` would be
consistent, and nonetheless entail all `φ(i)`"); [[bli-soto-a-inventory]] 057 (ii)
Kind: N+
Fidelity: exact (under the abstract layer)
Hyps: (a) none (all discharged) -/
theorem refute_propagation :
    propMeasure (univEvent propS 0) = ENNReal.ofReal (1 / 2) ∧
    ENNReal.ofReal (1 / 8) ≤ propMeasure ((univEvent propS 0)ᶜ ∩ ⋂ i, instEvent propS 0 i) ∧
    propMeasure (univEvent propS 0) < propMeasure (⋂ i, instEvent propS 0 i) := by
  have hq0 := chainPMF_nonneg propRule_inUnit 3
  have hq1 := chainPMF_sum_one propRule 3
  refine ⟨?_, ?_, ?_⟩
  · unfold propMeasure univEvent
    rw [extrapolate_sentence, prop_val_univ]
    norm_num
  · unfold propMeasure
    have h := hidden_le_measure propS propEnum propBase 0 hq0 hq1 prop_baseAxConsistent 3 propC
      prop_lev prop_notU prop_entails
    rw [sotoPMF_propC] at h
    have h' : ENNReal.ofReal (1 / 8) ≤
        (extrapolate propS propEnum propBase hq0) ((univEvent propS 0)ᶜ ∩ ⋂ i, instEvent propS 0 i) := by
      convert h using 2; norm_num
    exact h'
  · unfold propMeasure
    exact gaifman_lt_of_hiddenUniversal propS propEnum propBase 0 hq0 hq1 prop_baseAxConsistent
      prop_hiddenUniversal

end Cleanroom.Bli.BliExtrapolation
